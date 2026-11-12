module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeArrow
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonHomGluing

/-!
概要：元 unit パラメータ比較と同じ閉零成分の厳密変換を、実 Hom gluing 比較辺へ照合する。
方針：二実像小模型の全 Hom と、同じ閉射・閉元対応を使う。
規約：元比較射を変更しない。使われ方：中央射の実閉辺と native 全変換の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E P : Type (u + 1))
  [DGCategory R E] [Small.{u} E] [DGCategory R P]
  (F G : DGFunctor R P (PerfectDGModule R E))
  (τ : DGFunctorParamTrans R P (PerfectDGModule R E) (𝟙_ (Complex R)) F G)
  (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "T" => DGPerfectComparisonBase R E F G
local notation "L" => dgPerfectComparisonFirst R E F G
local notation "M" => dgPerfectComparisonSecond R E F G
local notation "X" => dgPerfectComparisonFamily R E F G

/-- 概要：同じ厳密変換の小模型内閉射は元 Hom gluing の実比較辺。
方針：元閉零成分の同定と全 Hom 恒等作用で閉射を回収する。
規約：元実像・元閉射を保持。使われ方：実中央射と同じ全 interval の接続。 -/
lemma dgPerfectComparisonStrictNatTrans_comparisonMap
    (hη : ∀ x, (η.app x).val = (cycleFromUnit _ (τ.app x)).val) (x : P) :
    (closedHomEquiv R (T) ((L).obj x) ((M).obj x)).symm
      ((dgSmallPerfectEnvelopeStrictNatTrans R E (P ⊕ P) (X) P F G
        Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl) η).app x) =
      dgPerfectComparisonMap R E F G τ x := by
  apply (closedHomEquiv R (T) ((L).obj x) ((M).obj x)).injective
  apply (Equiv.apply_symm_apply _ _).trans
  apply Subtype.ext
  let a : 𝟙_ (Complex R) ⟶ (F.obj x ⟶[Complex R] G.obj x) := τ.app x
  change (η.app x).val = (cycleFromUnit _ (a ≫ 𝟙 _)).val
  exact (hη x).trans
    (congrArg (fun k : 𝟙_ (Complex R) ⟶ (F.obj x ⟶[Complex R] G.obj x) =>
      (cycleFromUnit _ k).val) (Category.comp_id a).symm)

end SerrePositivity.KST.SConstruction
