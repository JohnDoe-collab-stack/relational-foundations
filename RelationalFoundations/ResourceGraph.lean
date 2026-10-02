import RelationalFoundations.DemandClosure
set_option genInjectivity false

/-!
# Finite constituted resources with historical references

Shapes and addresses are structural. Their cardinality is read afterward.
Every reference in a new expression addresses the support already produced.
Reuse reads that resource directly; it never reconstructs a request from its
value. Internal expression positions and historical references remain distinct.
-/

namespace RelationalFoundations.ResourceGraph
open DemandClosure
universe u v

inductive Shape where
  | leaf
  | branch (left right : Shape)

inductive Position : Shape → Type where
  | root {shape : Shape} : Position shape
  | left {first second : Shape} : Position first → Position (.branch first second)
  | right {first second : Shape} : Position second → Position (.branch first second)

inductive Layout where
  | initial (shape : Shape)
  | extend (previous : Layout) (shape : Shape)

inductive Address : Layout → Type where
  | initial {shape : Shape} : Position shape → Address (.initial shape)
  | old {previous : Layout} {shape : Shape} : Address previous → Address (.extend previous shape)
  | fresh {previous : Layout} {shape : Shape} : Position shape → Address (.extend previous shape)

inductive Expr (Token : Type u) (Reference : Type v) : Shape → Type (max u v) where
  | empty : Expr Token Reference .leaf
  | emit (token : Token) : Expr Token Reference .leaf
  | reuse (reference : Reference) : Expr Token Reference .leaf
  | join {left right : Shape} : Expr Token Reference left → Expr Token Reference right →
      Expr Token Reference (.branch left right)

inductive Node (Token : Type u) (Reference : Type v) where
  | empty
  | emit (token : Token)
  | reuse (reference : Reference)
  | join (left right : Reference)

namespace Node
variable {Token : Type u} {A B C : Type v}

def map (f : A → B) : Node Token A → Node Token B
  | .empty => .empty
  | .emit token => .emit token
  | .reuse reference => .reuse (f reference)
  | .join left right => .join (f left) (f right)

def inputs : Node Token A → List A
  | .empty => []
  | .emit _ => []
  | .reuse reference => [reference]
  | .join left right => [left, right]

def eval (read : A → List Token) : Node Token A → List Token
  | .empty => []
  | .emit token => [token]
  | .reuse reference => read reference
  | .join left right => read left ++ read right

theorem map_comp (f : A → B) (g : B → C) (node : Node Token A) :
    (node.map f).map g = node.map (fun a => g (f a)) := by
  cases node <;> rfl

theorem map_id (node : Node Token A) : node.map (fun a => a) = node := by
  cases node <;> rfl

theorem inputs_map (f : A → B) (node : Node Token A) :
    (node.map f).inputs = node.inputs.map f := by
  cases node <;> rfl

theorem eval_map (f : A → B) (read : B → List Token) (node : Node Token A) :
    (node.map f).eval read = node.eval (fun a => read (f a)) := by
  cases node <;> rfl
end Node

namespace Expr
variable {Token : Type u} {Reference : Type v}

def eval (read : Reference → List Token) : {shape : Shape} → Expr Token Reference shape → List Token
  | _, .empty => []
  | _, .emit token => [token]
  | _, .reuse reference => read reference
  | _, .join left right => left.eval read ++ right.eval read

def readAt (read : Reference → List Token) : {shape : Shape} →
    (expression : Expr Token Reference shape) → Position shape → List Token
  | _, expression, .root => expression.eval read
  | _, .join left _, .left position => readAt read left position
  | _, .join _ right, .right position => readAt read right position

theorem readAt_root (read : Reference → List Token) {shape : Shape}
    (expression : Expr Token Reference shape) : expression.readAt read .root = expression.eval read := by
  cases expression <;> rfl

theorem eval_congr (first second : Reference → List Token) (same : ∀ r, first r = second r)
    {shape : Shape} (expression : Expr Token Reference shape) : expression.eval first = expression.eval second := by
  induction expression with
  | empty => rfl
  | emit _ => rfl
  | reuse reference => exact same reference
  | join left right ihLeft ihRight =>
      exact (congrArg (fun value => value ++ right.eval first) ihLeft).trans
        (congrArg (List.append (left.eval second)) ihRight)

theorem readAt_congr (first second : Reference → List Token) (same : ∀ r, first r = second r)
    {shape : Shape} (expression : Expr Token Reference shape) (position : Position shape) :
    expression.readAt first position = expression.readAt second position := by
  induction expression with
  | empty => cases position; rfl
  | emit _ => cases position; rfl
  | reuse reference => cases position; exact same reference
  | join left right ihLeft ihRight =>
      cases position with
      | root => exact eval_congr first second same (.join left right)
      | left p => exact ihLeft p
      | right p => exact ihRight p

def describe {A : Type v} (old : Reference → A) : {shape : Shape} →
    (expression : Expr Token Reference shape) → (fresh : Position shape → A) →
    Position shape → Node Token A
  | _, .empty, _, .root => .empty
  | _, .emit token, _, .root => .emit token
  | _, .reuse reference, _, .root => .reuse (old reference)
  | _, .join _ _, fresh, .root => .join (fresh (.left .root)) (fresh (.right .root))
  | _, .join left _, fresh, .left position => describe old left (fun p => fresh (.left p)) position
  | _, .join _ right, fresh, .right position => describe old right (fun p => fresh (.right p)) position

theorem describe_correct {A : Type v} (old : Reference → A) (read : A → List Token)
    {shape : Shape} (expression : Expr Token Reference shape) (fresh : Position shape → A)
    (new_values : ∀ p, read (fresh p) = expression.readAt (fun r => read (old r)) p)
    (position : Position shape) :
    (expression.describe old fresh position).eval read =
      expression.readAt (fun r => read (old r)) position := by
  induction expression with
  | empty => cases position; rfl
  | emit token => cases position; rfl
  | reuse reference => cases position; rfl
  | join left right ihLeft ihRight =>
      cases position with
      | root =>
          change read (fresh (.left .root)) ++ read (fresh (.right .root)) =
            left.eval (fun r => read (old r)) ++ right.eval (fun r => read (old r))
          have left_value := (new_values (.left .root)).trans (left.readAt_root _)
          have right_value := (new_values (.right .root)).trans (right.readAt_root _)
          exact (congrArg (fun value => value ++ read (fresh (.right .root))) left_value).trans
            (congrArg (List.append (left.eval (fun r => read (old r)))) right_value)
      | left p => exact ihLeft _ (fun q => new_values (.left q)) p
      | right p => exact ihRight _ (fun q => new_values (.right q)) p
end Expr

inductive Support (Token : Type u) : Layout → Type u where
  | initial {shape : Shape} : Expr Token Empty shape → Support Token (.initial shape)
  | extend {previous : Layout} {shape : Shape} : Support Token previous →
      Expr Token (Address previous) shape → Support Token (.extend previous shape)

namespace Support
variable {Token : Type u}

def read : {layout : Layout} → Support Token layout → Address layout → List Token
  | _, .initial expression, .initial position => expression.readAt Empty.elim position
  | _, .extend previous _, .old address => read previous address
  | _, .extend previous expression, .fresh position => expression.readAt (read previous) position

def nodeAt : {layout : Layout} → Support Token layout → Address layout → Node Token (Address layout)
  | _, .initial expression, .initial position => expression.describe Empty.elim Address.initial position
  | _, .extend previous _, .old address => (nodeAt previous address).map Address.old
  | _, .extend _ expression, .fresh position => expression.describe Address.old Address.fresh position

def dependencies {layout : Layout} (support : Support Token layout) (address : Address layout) :
    List (Address layout) := (support.nodeAt address).inputs

def Depends {layout : Layout} (support : Support Token layout) (parent child : Address layout) : Prop :=
  child ∈ support.dependencies parent

/-- Every resource, including every internal expression position, obeys its local rule. -/
theorem read_correct : {layout : Layout} → (support : Support Token layout) →
    (address : Address layout) → support.read address = (support.nodeAt address).eval support.read
  | _, .initial expression, .initial position => by
      have same := expression.readAt_congr Empty.elim (fun r => (Support.initial expression).read (Empty.elim r))
        (fun r => nomatch r) position
      exact same.trans (expression.describe_correct Empty.elim (read (.initial expression)) Address.initial
        (fun p => expression.readAt_congr _ _ (fun r => nomatch r) p) position).symm
  | _, .extend previous expression, .old address =>
      (read_correct previous address).trans (Node.eval_map Address.old (read (.extend previous expression)) _).symm
  | _, .extend previous expression, .fresh position =>
      (expression.describe_correct Address.old (read (.extend previous expression)) Address.fresh
        (fun _ => rfl) position).symm

theorem old_injective {layout : Layout} {shape : Shape} :
    Function.Injective (@Address.old layout shape) := by
  intro first second equality
  cases equality
  rfl

theorem old_fresh_distinct {layout : Layout} {shape : Shape}
    (old : Address layout) (fresh : Position shape) :
    Address.old (shape := shape) old ≠ Address.fresh (previous := layout) fresh := by
  intro equality
  cases equality
end Support

namespace Shape
def size : Shape → Nat
  | .leaf => 1
  | .branch left right => 1 + (size left + size right)

theorem size_positive (shape : Shape) : 0 < shape.size := by
  cases shape with
  | leaf => exact Nat.zero_lt_succ _
  | branch left right => exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_add_right 1 _)

def positions : (shape : Shape) → List (Position shape)
  | .leaf => [.root]
  | .branch left right => .root :: (positions left).map Position.left ++ (positions right).map Position.right

theorem positions_complete : (shape : Shape) → (position : Position shape) → position ∈ shape.positions
  | .leaf, .root => .head _
  | .branch _ _, .root => .head _
  | .branch left _, .left position => List.mem_cons_of_mem _
      (List.mem_append_left _ (FiniteList.mappedMember Position.left (positions_complete left position)))
  | .branch _ right, .right position => List.mem_cons_of_mem _
      (List.mem_append_right _ (FiniteList.mappedMember Position.right (positions_complete right position)))

theorem positions_length (shape : Shape) : shape.positions.length = shape.size := by
  induction shape with
  | leaf => rfl
  | branch left right ihLeft ihRight =>
      simp only [positions, List.length_cons, FiniteList.appendLength, FiniteList.mapLength, size]
      rw [ihLeft, ihRight, Nat.succ_add, Nat.add_comm 1]
end Shape

namespace Layout
def size : Layout → Nat
  | .initial shape => shape.size
  | .extend previous shape => previous.size + shape.size

def addresses : (layout : Layout) → List (Address layout)
  | .initial shape => shape.positions.map Address.initial
  | .extend previous shape => previous.addresses.map Address.old ++ shape.positions.map Address.fresh

theorem addresses_complete : (layout : Layout) → (address : Address layout) → address ∈ layout.addresses
  | .initial shape, .initial position => FiniteList.mappedMember Address.initial (shape.positions_complete position)
  | .extend previous _, .old address => List.mem_append_left _
      (FiniteList.mappedMember Address.old (addresses_complete previous address))
  | .extend _ shape, .fresh position => List.mem_append_right _
      (FiniteList.mappedMember Address.fresh (shape.positions_complete position))

theorem addresses_length (layout : Layout) : layout.addresses.length = layout.size := by
  induction layout with
  | initial shape => exact (FiniteList.mapLength _ _).trans shape.positions_length
  | extend previous shape ih =>
      simp only [addresses, FiniteList.appendLength, FiniteList.mapLength, size]
      rw [ih, shape.positions_length]
end Layout

/-- Extension evidence retains each actual expression with its historical references. -/
inductive Extension {Token : Type u} {initialLayout : Layout} (initial : Support Token initialLayout) :
    {finalLayout : Layout} → Support Token finalLayout → Type u where
  | refl : Extension initial initial
  | step {middleLayout : Layout} {middle : Support Token middleLayout} {shape : Shape} :
      Extension initial middle → (expression : Expr Token (Address middleLayout) shape) →
      Extension initial (.extend middle expression)

namespace Extension
variable {Token : Type u} {a b c : Layout}
variable {first : Support Token a} {second : Support Token b} {third : Support Token c}

def compose (initial : Extension first second) : {c : Layout} → {third : Support Token c} →
    Extension second third → Extension first third
  | _, _, .refl => initial
  | _, _, .step previous expression => .step (compose initial previous) expression

def embed : {b : Layout} → {second : Support Token b} → Extension first second → Address a → Address b
  | _, _, .refl, address => address
  | _, _, .step previous _, address => .old (embed previous address)

theorem embed_injective (extension : Extension first second) : Function.Injective extension.embed := by
  induction extension with
  | refl => exact fun _ _ equality => equality
  | step previous expression ih =>
      intro left right equality
      exact ih (Support.old_injective equality)

theorem read_preserved (extension : Extension first second) (address : Address a) :
    second.read (extension.embed address) = first.read address := by
  induction extension with
  | refl => rfl
  | step previous expression ih => exact ih

theorem node_preserved (extension : Extension first second) (address : Address a) :
    second.nodeAt (extension.embed address) = (first.nodeAt address).map extension.embed := by
  induction extension with
  | refl => exact (Node.map_id _).symm
  | step previous expression ih =>
      change (Support.nodeAt _ (previous.embed address)).map Address.old = _
      exact (congrArg (Node.map Address.old) ih).trans (Node.map_comp _ _ _)

theorem dependencies_preserved (extension : Extension first second) (address : Address a) :
    second.dependencies (extension.embed address) = (first.dependencies address).map extension.embed :=
  (congrArg Node.inputs (extension.node_preserved address)).trans (Node.inputs_map _ _)

theorem relation_preserved (extension : Extension first second) {parent child : Address a}
    (related : first.Depends parent child) : second.Depends (extension.embed parent) (extension.embed child) := by
  change extension.embed child ∈ second.dependencies (extension.embed parent)
  rw [extension.dependencies_preserved]
  exact FiniteList.mappedMember extension.embed related

theorem splitMember {A : Type} {value head : A} {tail : List A}
    (member : value ∈ head :: tail) : value = head ∨ value ∈ tail :=
  match member with
  | .head _ => .inl rfl
  | .tail _ rest => .inr rest

theorem mapped_member_reflects {A B : Type} (f : A → B) (injective : Function.Injective f) {value : A}
    (items : List A) (member : f value ∈ items.map f) : value ∈ items := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      cases splitMember member with
      | inl same =>
          have equality : value = head := injective same
          cases equality
          exact .head _
      | inr rest => exact .tail _ (ih rest)

theorem relation_reflected (extension : Extension first second) {parent child : Address a}
    (related : second.Depends (extension.embed parent) (extension.embed child)) : first.Depends parent child := by
  change extension.embed child ∈ second.dependencies (extension.embed parent) at related
  rw [extension.dependencies_preserved] at related
  exact mapped_member_reflects extension.embed extension.embed_injective _ related

theorem embed_compose (initial : Extension first second) (continuation : Extension second third)
    (address : Address a) :
    (initial.compose continuation).embed address = continuation.embed (initial.embed address) := by
  induction continuation with
  | refl => rfl
  | step previous expression ih => exact congrArg Address.old ih

theorem compose_associative {d : Layout} {fourth : Support Token d}
    (one : Extension first second) (two : Extension second third) (three : Extension third fourth) :
    (one.compose two).compose three = one.compose (two.compose three) := by
  induction three with
  | refl => rfl
  | step previous expression ih => exact congrArg (fun growth => Extension.step growth expression) ih
end Extension

namespace Enumeration
/-- Recover a mapped occurrence using its actual membership evidence. -/
theorem map_origin {A B : Type} (f : A → B) (items : List A) {value : B}
    (member : value ∈ items.map f) : ∃ original, original ∈ items ∧ f original = value := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      cases Extension.splitMember member with
      | inl equality => exact ⟨head, .head _, equality.symm⟩
      | inr rest =>
          obtain ⟨original, member, equality⟩ := ih rest
          exact ⟨original, .tail _ member, equality⟩

theorem append_cases {A : Type} {value : A} (first second : List A)
    (member : value ∈ first ++ second) : value ∈ first ∨ value ∈ second := by
  induction first with
  | nil => exact .inr member
  | cons head tail ih =>
      cases Extension.splitMember member with
      | inl equality => cases equality; exact .inl (.head _)
      | inr rest =>
          cases ih rest with
          | inl member => exact .inl (.tail _ member)
          | inr member => exact .inr member

theorem nodup_map {A B : Type} (f : A → B) (injective : Function.Injective f)
    {items : List A} (unique : items.Nodup) : (items.map f).Nodup := by
  induction unique with
  | nil => exact .nil
  | @cons head tail distinct unique ih =>
      apply List.Pairwise.cons _ ih
      intro value member equality
      obtain ⟨original, member, origin⟩ := map_origin f tail member
      exact distinct original member (injective (equality.trans origin.symm))

theorem nodup_append {A : Type} {first second : List A} (one : first.Nodup) (two : second.Nodup)
    (separate : ∀ a, a ∈ first → ∀ b, b ∈ second → a ≠ b) : (first ++ second).Nodup := by
  induction one with
  | nil => exact two
  | @cons head tail distinct unique ih =>
      apply List.Pairwise.cons
      · intro value member
        cases append_cases tail second member with
        | inl member => exact distinct value member
        | inr member => exact separate head (.head _) value member
      · exact ih (fun a member b other => separate a (.tail _ member) b other)
end Enumeration

namespace Shape
theorem positions_nodup (shape : Shape) : shape.positions.Nodup := by
  induction shape with
  | leaf => exact .cons (fun _ impossible => nomatch impossible) .nil
  | branch left right ihLeft ihRight =>
      apply List.Pairwise.cons
      · intro value member equality
        cases Enumeration.append_cases _ _ member with
        | inl member =>
            obtain ⟨position, _, origin⟩ := Enumeration.map_origin Position.left _ member
            have impossible := equality.trans origin.symm
            cases impossible
        | inr member =>
            obtain ⟨position, _, origin⟩ := Enumeration.map_origin Position.right _ member
            have impossible := equality.trans origin.symm
            cases impossible
      · apply Enumeration.nodup_append
          (Enumeration.nodup_map Position.left (fun _ _ equality => by cases equality; rfl) ihLeft)
          (Enumeration.nodup_map Position.right (fun _ _ equality => by cases equality; rfl) ihRight)
        intro first member second other equality
        obtain ⟨one, _, originOne⟩ := Enumeration.map_origin Position.left _ member
        obtain ⟨two, _, originTwo⟩ := Enumeration.map_origin Position.right _ other
        have impossible := originOne.trans (equality.trans originTwo.symm)
        cases impossible
end Shape

namespace Layout
/-- Enumeration contains every constituted address exactly once. -/
theorem addresses_nodup (layout : Layout) : layout.addresses.Nodup := by
  induction layout with
  | initial shape =>
      exact Enumeration.nodup_map Address.initial
        (fun _ _ equality => by cases equality; rfl) shape.positions_nodup
  | extend previous shape ih =>
      apply Enumeration.nodup_append
        (Enumeration.nodup_map Address.old Support.old_injective ih)
        (Enumeration.nodup_map Address.fresh (fun _ _ equality => by cases equality; rfl) shape.positions_nodup)
      intro first member second other equality
      obtain ⟨one, _, originOne⟩ := Enumeration.map_origin Address.old _ member
      obtain ⟨two, _, originTwo⟩ := Enumeration.map_origin Address.fresh _ other
      exact Support.old_fresh_distinct one two (originOne.trans (equality.trans originTwo.symm))
end Layout

end RelationalFoundations.ResourceGraph
