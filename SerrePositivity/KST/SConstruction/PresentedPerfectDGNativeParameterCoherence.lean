module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeFamilyCoherence

/-! # Perf 宇宙へ移した native Kan 入力の結合・単位
概要：元の全 native Kan 入力を ULift した写像空間の合成と単位に、厳密な圏法則を与える。
方針：全単体の ULift と core の包含で、元の native 関手族の結合・単位へ帰着する。
規約：元の厳密 dg 関手の恒等頂点を単位に使う。使われ方：豊穣 Perf 入力の宇宙移送。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E B T : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A B] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} B] [Small.{u} T]

omit [Small.{u} T] in
/-- 出力宇宙へ移した元の Kan 入力合成は、元の直積の結合同型を介して結合的。 -/
lemma presentedPerfectDGNativeParameterComp_associativity :
    (presentedPerfectDGNativeParameterComp A D E B ⊗ₘ
        𝟙 (presentedPerfectDGNativeParameter A B T)) ≫
        presentedPerfectDGNativeParameterComp A D B T =
      (α_ (presentedPerfectDGNativeParameter A D E) (presentedPerfectDGNativeParameter A E B)
        (presentedPerfectDGNativeParameter A B T)).hom ≫
        (𝟙 (presentedPerfectDGNativeParameter A D E) ⊗ₘ
          presentedPerfectDGNativeParameterComp A E B T) ≫
        presentedPerfectDGNativeParameterComp A D E T := by
  ext n p
  rcases p with ⟨⟨s, t⟩, r⟩
  apply ULift.ext
  apply Subtype.ext
  exact dgFunctorNativeComposeSimplex_associativity A D E B T s.down.val t.down.val r.down.val

omit [DGCategory A B] [DGCategory A T] [Small.{u} B] [Small.{u} T] [Small.{u} E] in
/-- 元の恒等関手の単位射は、ULift 後の native Kan 入力合成の左単位。 -/
lemma presentedPerfectDGNativeParameterComp_left_unit :
    (presentedPerfectDGNativeParameterPoint A D D (DGFunctor.id D) ⊗ₘ
        𝟙 (presentedPerfectDGNativeParameter A D E)) ≫
        presentedPerfectDGNativeParameterComp A D D E =
      (λ_ (presentedPerfectDGNativeParameter A D E)).hom := by
  ext n p
  rcases p with ⟨a, s⟩
  apply ULift.ext
  apply Subtype.ext
  change dgFunctorNativeComposeSimplex A D D E
    (((presentedPerfectDGNativeParameterPoint A D D (DGFunctor.id D)).app n a).down.val)
      s.down.val = s.down.val
  rw [presentedPerfectDGNativeParameterPoint_app, ← dgFunctorNativeIdentitySimplex_point]
  exact dgFunctorNativeComposeSimplex_left_unit A D E s.down.val

omit [DGCategory A B] [DGCategory A T] [Small.{u} B] [Small.{u} T] in
/-- 元の恒等関手の単位射は、ULift 後の native Kan 入力合成の右単位。 -/
lemma presentedPerfectDGNativeParameterComp_right_unit :
    (𝟙 (presentedPerfectDGNativeParameter A D E) ⊗ₘ
        presentedPerfectDGNativeParameterPoint A E E (DGFunctor.id E)) ≫
        presentedPerfectDGNativeParameterComp A D E E =
      (ρ_ (presentedPerfectDGNativeParameter A D E)).hom := by
  ext n p
  rcases p with ⟨s, a⟩
  apply ULift.ext
  apply Subtype.ext
  change dgFunctorNativeComposeSimplex A D E E s.down.val
    (((presentedPerfectDGNativeParameterPoint A E E (DGFunctor.id E)).app n a).down.val) =
      s.down.val
  rw [presentedPerfectDGNativeParameterPoint_app, ← dgFunctorNativeIdentitySimplex_point]
  exact dgFunctorNativeComposeSimplex_right_unit A D E s.down.val

end SerrePositivity.KST.SConstruction
