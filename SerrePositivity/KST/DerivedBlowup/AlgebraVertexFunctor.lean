module

public import SerrePositivity.KST.DerivedBlowup.AlgebraVertex

/-!
概要：KST §3.1 の dg 代数の射に沿う一対象正規表示の dg 関手。
方針：対象を標準点へ送り、全 Hom でモノイド対象の指定射を使う。
規約：合成・恒等を共通基底環上の dg 関手の等式として保つ。
使われ方：全有限重なりの係数図式の一対象表示。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable {R : Type u} [CommRing R]

/-- 概要：dg 代数の指定射を一対象正規表示の dg 関手へ送る。
方針：単位・積保存はモノイド対象の射の公理をそのまま使う。
規約：KST §3.1。使われ方：局所代数の遷移を対象移送なしで扱う。 -/
def algebraVertexMap {A B : Mon (Complex R)} (f : A ⟶ B) :
    DGFunctor R (AlgebraVertex A) (AlgebraVertex B) where
  obj _ := .point
  map _ _ := f.hom
  map_id _ := IsMonHom.one_hom f.hom
  map_comp _ _ _ := IsMonHom.mul_hom f.hom

/-- 概要：正規表示はモノイド対象の射の合成を保つ。
方針：対象写像はともに標準点で、Hom では元の射の合成公式を使う。
規約：KST §3.1。使われ方：正規表示の局所遷移の三重整合性。 -/
theorem algebraVertexMap_comp {A B C : Mon (Complex R)} (f : A ⟶ B) (g : B ⟶ C) :
    (algebraVertexMap f).comp (algebraVertexMap g) = algebraVertexMap (f ≫ g) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact (Mon.comp_hom' f g).symm

/-- 概要：正規表示はモノイド対象の恒等射を恒等 dg 関手へ送る。
方針：一対象性と Hom 上の恒等公式を使う。
規約：KST §3.1。使われ方：局所遷移の単位条件。 -/
theorem algebraVertexMap_id (A : Mon (Complex R)) :
    algebraVertexMap (𝟙 A) = DGFunctor.id (AlgebraVertex A) := by
  refine EnrichedFunctor.ext (Complex R) (fun x => by cases x; rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact Mon.id_hom' A

end SerrePositivity.KST.DerivedBlowup
