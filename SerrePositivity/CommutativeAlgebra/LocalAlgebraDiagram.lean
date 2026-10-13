module

public import SerrePositivity.CommutativeAlgebra.AlgebraSystemReindex

/-! # 局所代数の図式とその制限

環・構造・遷移・指定終域への写像を格納する通常の図式。
有向図式の法則、平坦性、剰余体の像は別に検証する。
制限には環の構造も含め、型だけの同一視に依存しない。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing
universe u v
variable (B K : Type u) [CommRing B] [IsLocalRing B] [CommRing K] [Algebra B K]

/-- 局所B代数の族、遷移写像、指定終域への写像。 -/
structure LocalAlgebraDiagram (ι : Type v) [Preorder ι] where
  obj : ι → Type u
  [ring : ∀ i, CommRing (obj i)]
  [localRing : ∀ i, IsLocalRing (obj i)]
  [algebra : ∀ i, Algebra B (obj i)]
  [baseLocal : ∀ i, IsLocalHom (algebraMap B (obj i))]
  map : ∀ i j, i ≤ j → obj i →ₐ[B] obj j
  target : ∀ i, obj i →ₐ[B] K

attribute [instance] LocalAlgebraDiagram.ring LocalAlgebraDiagram.localRing
  LocalAlgebraDiagram.algebra LocalAlgebraDiagram.baseLocal

variable {B K} {ι κ : Type v} [Preorder ι] [Preorder κ]

omit [IsLocalRing B] in
/-- 図式の一致には、環の台だけでなく環・代数の構造と写像の一致が必要。
局所性と基底写像の局所性は命題なので証明無関係性で一致する。 -/
theorem LocalAlgebraDiagram.ext (D E : LocalAlgebraDiagram B K ι)
    (hobj : D.obj = E.obj) (hring : HEq D.ring E.ring)
    (halg : HEq D.algebra E.algebra) (hmap : HEq D.map E.map)
    (htarget : HEq D.target E.target) : D = E := by
  cases D
  cases E
  cases hobj
  cases hring
  cases halg
  cases hmap
  cases htarget
  rfl

/-- 単調な添字写像で環の構造と写像を同時に制限する。 -/
def LocalAlgebraDiagram.reindex (D : LocalAlgebraDiagram B K ι)
    (r : κ → ι) (hr : Monotone r) : LocalAlgebraDiagram B K κ where
  obj j := D.obj (r j)
  map := algebraSystemReindexMap D.obj D.map r hr
  target j := D.target (r j)

omit [IsLocalRing B] in
@[simp] theorem LocalAlgebraDiagram.reindex_id (D : LocalAlgebraDiagram B K ι) :
    D.reindex id monotone_id = D := rfl

omit [IsLocalRing B] in
theorem LocalAlgebraDiagram.reindex_comp {J : Type v} [Preorder J]
    (D : LocalAlgebraDiagram B K ι) (r : κ → ι) (hr : Monotone r)
    (s : J → κ) (hs : Monotone s) :
    (D.reindex r hr).reindex s hs = D.reindex (r ∘ s) (hr.comp hs) := rfl

/-- 再帰の全域化の既定値。正しい剰余体の像や平坦性の主張は含めない。 -/
def LocalAlgebraDiagram.constant : LocalAlgebraDiagram B K ι where
  obj _ := B
  baseLocal _ := by
    change IsLocalHom (RingHom.id B)
    infer_instance
  map _ _ _ := AlgHom.id B B
  target _ := Algebra.ofId B K

instance : Nonempty (LocalAlgebraDiagram B K ι) := ⟨LocalAlgebraDiagram.constant⟩

end SerrePositivity
