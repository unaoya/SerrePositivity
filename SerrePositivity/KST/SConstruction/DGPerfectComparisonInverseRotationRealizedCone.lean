module
public import SerrePositivity.KST.SConstruction.DGHomGluingInverseRotationCone
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonHomGluing
public import SerrePositivity.KST.SConstruction.DGPerfectRealization

/-!
概要：元比較の実逆回転 cone の指定成分を、同じ二実像包絡の実評価で元第二関手へ戻す。
方針：元実加群比較を同じ実 realization で写し、元代表加群比較を合成する。
規約：逆回転小基底の Yoneda 評価前の成分。全関手族の自然性は別工程。
使われ方：実中央射・実差の合成比較の実候補と成分同値判定。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type w} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (PerfectDGModule R E))
  (τ : DGFunctorParamTrans R P (PerfectDGModule R E) (𝟙_ (Complex R)) F G)
local notation "T" => DGPerfectComparisonBase R E F G
local notation "I" => DGFunctor.id (T)
local notation "H" => dgPerfectComparisonHomGluingFunctor R E F G τ
local notation "J" => dgSmallPerfectEnvelopeInclusion R E (P ⊕ P)
  (dgPerfectComparisonFamily R E F G)
local notation "V" => dgPerfectRealization R (T) E (J)

/-- 概要：同じ実逆回転 cone を元第二関手の同じ加群像へ戻す指定射。
方針：元加群比較と元二像包絡の実 realization・元代表比較を合成する。
規約：対象別存在選択を使わない。使われ方：実商合成全比較の指定成分。 -/
def dgPerfectComparisonInverseRotationRealizedConeComparison (x : P) :
    (V).onClosed.obj
      (moduleCone R (T) (dgHomGluingInverseRotationModuleMap R (T) (T) (T) (I) (I)
        ((H).obj x))) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x).val :=
  (V).onClosed.map
    (dgHomGluingInverseRotationConeComparison R (T) (T) (T) (I) (I) ((H).obj x)) ≫
    (dgPerfectRealizationRepresentableIso R (T) E (J)
      ((dgPerfectComparisonSecond R E F G).obj x)).hom

private lemma realizedCompositeIsIso
    {A₀ B₀ C₀ : ModuleCategory R E} (a : A₀ ⟶ B₀) (e : B₀ ≅ C₀)
    [IsIso ((moduleToHomotopy R E).map a)] :
    IsIso ((moduleToHomotopy R E).map (a ≫ e.hom)) := by
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 概要：同じ実評価後の指定成分は元 K(E) で同値。
方針：元実逆回転比較の K(T) 同値を同じ dg realization で写す。
規約：全関手族比較は別途必要。使われ方：合成比較の実成分認証。 -/
lemma dgPerfectComparisonInverseRotationRealizedConeComparison_isIso (x : P) :
    IsIso ((moduleToHomotopy R E).map
      (dgPerfectComparisonInverseRotationRealizedConeComparison R E F G τ x)) := by
  haveI := dgHomGluingInverseRotationConeComparison_isIso R (T) (T) (T) (I) (I) ((H).obj x)
  haveI : IsIso ((moduleToHomotopy R E).map ((V).onClosed.map
      (dgHomGluingInverseRotationConeComparison R (T) (T) (T) (I) (I) ((H).obj x)))) := by
    change IsIso ((V).onHomotopy.map ((moduleToHomotopy R (T)).map
      (dgHomGluingInverseRotationConeComparison R (T) (T) (T) (I) (I) ((H).obj x))))
    infer_instance
  exact realizedCompositeIsIso R E
    ((V).onClosed.map
      (dgHomGluingInverseRotationConeComparison R (T) (T) (T) (I) (I) ((H).obj x)))
    (dgPerfectRealizationRepresentableIso R (T) E (J)
      ((dgPerfectComparisonSecond R E F G).obj x))

end SerrePositivity.KST.SConstruction
