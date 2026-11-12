module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullCoherence

/-!
概要：実零合成の全比較空間を、同じ固定 ν の豊穣 Hom へ写す。
方針：可縮 Kan 空間の全辺の可逆性で完全関手圏の core へ持ち上げる。
規約：元の二つの実合成を端点として保つ。全四角形比較とは区別する。
使われ方：coherent nerve の実面比較の端点 Hom 充填。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "Src" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "Tgt" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Space" => DGOdotMilnorNuNullCoherenceSpace R d

/-- 概要：実零合成の全比較を同じ豊穣 Hom の自然同値として保持する。
方針：可縮空間の辺の可逆性を完全関手圏へ写して core へ持ち上げる。
規約：高次単体も含む射である。使われ方：全境界の Hom 内充填。 -/
def dgOdotMilnorNuNullCoherenceHom :
    (Space) ⟶ SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (Src) (Tgt) := by
  letI : KanComplex (Space) := (dgOdotMilnorNuNullCoherenceSpace_contractible R d h).kanComplex
  change (Space) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1}) : SSet)
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices _).ι (fun s => ?_)
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (Space)) _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (by rfl)).mp (hs.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices _).ι)

/-- 概要：豊穣 Hom への持ち上げは元の実完全関手を全単体で保つ。
方針：core 持ち上げの定義を使用する。
規約：頂点の同型類だけに弱めない。使われ方：元の実面の端点 Hom との照合。 -/
lemma dgOdotMilnorNuNullCoherenceHom_inclusion :
    dgOdotMilnorNuNullCoherenceHom R d h ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (Src) (Tgt) : SSet.{u + 1})).ι := rfl

/-- 概要：実商合成の比較空間内の頂点は、元の豊穣 Hom の射そのもの。
方針：core への頂点持ち上げの定義を使用する。
規約：関手を選び直さない。使われ方：同じ包含・商の合成端点の回収。 -/
lemma dgOdotMilnorNuNullCoherenceHom_composite :
    (dgOdotMilnorNuNullCoherenceHom R d h).app (Opposite.op ⦋0⦌)
      (dgOdotMilnorNuNullCompositeVertex R d h) =
        SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (Src) (Tgt)
          (dgOdotMilnorNuNullComposite R d) := by
  apply Subtype.ext
  rfl

/-- 概要：元の実零角経由の合成も同じ豊穣 Hom の頂点として回収する。
方針：同じ core 持ち上げの頂点の値を取る。
規約：零角を標準零圏に置換しない。使われ方：実面のもう一方の経路の回収。 -/
lemma dgOdotMilnorNuNullCoherenceHom_top :
    (dgOdotMilnorNuNullCoherenceHom R d h).app (Opposite.op ⦋0⦌)
      (dgOdotMilnorNuNullTopCompositeVertex R d) =
        SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (Src) (Tgt)
          (dgOdotMilnorNuNullTopComposite R d) := by
  apply Subtype.ext
  rfl

/-- 概要：実零化面の元の二経路は固定 ν の完全関手として厳密に一致する。
方針：元の全対象商延長の合成式と同じラベル付き Perf 関手の合成保存を使う。
規約：実二単体の一致は別に検証する。使われ方：相対 Hom 充填の共通端点。 -/
lemma dgOdotMilnorNuNullTopComposite_eq :
    dgOdotMilnorNuNullTopComposite R d = dgOdotMilnorNuNullComposite R d := by
  have map_comp {P Q T : PerfDGInput.{u, u + 1} R} (f : P ⟶ Q) (g : Q ⟶ T) :
      (dgKInputNuMap R (f ≫ g)).hom =
        (dgKInputNuMap R f).hom ≫ (dgKInputNuMap R g).hom := by
    have e := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.hom
      ((presentedPerfectDGStableCategoryFunctor R).map_comp f g)
    change (presentedPerfectDGExactMap R (f ≫ g)).hom =
      (presentedPerfectDGExactMap R f).hom ≫ (presentedPerfectDGExactMap R g).hom at e
    rw [← dgKInputNuMap_eq R, ← dgKInputNuMap_eq R, ← dgKInputNuMap_eq R] at e
    exact e
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext
  change (dgKInputNuMap R (dgFixedNullLeft R
    (A := dgOdotMilnorFlatKernelInput R d))).hom ≫
      (dgKInputNuMap R (dgFixedNullTop R (dgOdotMilnorFlatKernelContracted R d))).hom =
        (dgKInputNuMap R (dgOdotMilnorFlatKernelInputMap R d)).hom ≫
          (dgKInputNuMap R (dgOdotMilnorCellProjectionInputMap R d)).hom
  rw [← map_comp, dgFixedNull_comm R (dgOdotMilnorFlatKernelInputMap R d)
    (dgOdotMilnorCellProjectionInputMap R d) (dgOdotMilnorFlatKernelContracted R d) rfl,
    map_comp]

end SerrePositivity.KST.SConstruction
