module
public import SerrePositivity.KST.Fibration.ZeroMiddleReconstructionSupply
public import SerrePositivity.KST.Fibration.ZeroMiddleControlledPrismHomotopy

/-!
概要：採用済み因子分解三単体族の供給を、同じ零中間二胞体へ代入する。
方針：元の core 包含・零値全 S• 比較・第二短辺を固定して三面と長 Hom を回収する。
規約：Ind-S (9b) の命題を明示引数に取り、その存在は主張しない。
使われ方：K-6 c4 の制御充填を固定三面比較へ渡す実利用側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1})

/-- 概要：同じ未変更の三面と元の長 Hom を保持する実因子分解族の条件。
方針：二つの合成面と元の native 面を全パラメータで指定する。
規約：同じ零中間二胞体専用で、一般三単体の充填 API ではない。
使われ方：Ind-S (9b) への実代入と指定欠面の読出し。 -/
def zeroMiddleFactorizationTetraCondition
    (F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : Prop :=
  (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ F =
    fst (Δ[2] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm (zeroMiddleFullSKanLastTriangle s hZ).simplex ∧
  (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ F =
    fst (Δ[2] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s) ∧
  (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ F =
    fst (Δ[2] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm (zeroMiddleFullSKanFirstTriangle s hZ).simplex ∧
  ∀ k : K _⦋0⦌,
    let t := SSet.yonedaEquiv (lift (𝟙 (Δ[3] : SSet.{u + 1})) (SSet.const k) ≫ F)
    let a := SSet.yonedaEquiv (lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const k) ≫
      fst (Δ[2] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
          (Opposite.op ⦋2⦌) s))
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 4) t).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      (a.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)

/-- 概要：供給命題に条件付きで、同じ三面と指定長 Hom を保つ実族が得られる。
方針：元の core 包含と全 S• 比較の厳密因子分解を Ind-S (9b) に代入する。
規約：命題の証明や無条件の再構成は主張しない。
使われ方：構成済みの同じ F だけを固定三面 fiber の比較へ渡す。 -/
theorem zeroMiddleFactorizationTetra_exists (h9b : zeroMiddleFactorizationTetraSupply.{u}) :
    ∃ F, zeroMiddleFactorizationTetraCondition s hZ K F := by
  let f : stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩) ⟶
      fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (s.obj ⟨ULift.up 0⟩))
  let g := zeroMiddleFullSKanComparison s hZ
  let h := stableCoreSingleKanMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 s))
  let T := fst (Δ[2] : SSet.{u + 1}) K ≫
    SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
      (Opposite.op ⦋2⦌) s)
  apply h9b _ _ _ _ f g h K T
  · dsimp only [T]
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]
    apply congrArg (fun t => fst (Δ[1] : SSet.{u + 1}) K ≫ t)
    have he := stdSimplex.δ_comp_yonedaEquiv_symm (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s) (2 : Fin 3)
    exact he.trans (congrArg SSet.yonedaEquiv.symm
      ((zeroMiddleCoreSingleKanTriangle_first s).trans
        (congrArg (fun q => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge)
          (zeroMiddleFullSKanComparison_first s hZ).symm)))
  · dsimp only [T]
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]
    apply congrArg (fun t => fst (Δ[1] : SSet.{u + 1}) K ≫ t)
    have he := stdSimplex.δ_comp_yonedaEquiv_symm (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s) (0 : Fin 3)
    exact he.trans (congrArg SSet.yonedaEquiv.symm (zeroMiddleCoreSingleKanTriangle_last s))

/-- 概要：供給命題から選んだ同じ実因子分解族。
方針：元の三面・長 Hom を保持する存在命題から選ぶ。
規約：供給命題は明示引数で、存在は無条件化しない。
使われ方：元の三角柱と固定三面比較の共通する実入力。 -/
def zeroMiddleFactorizationTetra (h9b : zeroMiddleFactorizationTetraSupply.{u}) :
    (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (zeroMiddleFactorizationTetra_exists s hZ K h9b).choose

/-- 概要：選んだ同じ実族は三面と指定長 Hom の条件を保持する。
方針：選択に用いた同じ命題の回収式を使う。
規約：別の充填へ置き換えない。
使われ方：固定三面 fiber と欠面の全 native Hom の照合。 -/
theorem zeroMiddleFactorizationTetra_spec (h9b : zeroMiddleFactorizationTetraSupply.{u}) :
    zeroMiddleFactorizationTetraCondition s hZ K
      (zeroMiddleFactorizationTetra s hZ K h9b) :=
  (zeroMiddleFactorizationTetra_exists s hZ K h9b).choose_spec

/-- 概要：同じ制御上側の各指定点の全 native Hom は元の二胞体の全 Hom そのもの。
方針：供給された末尾の HEq で、元の定値二胞体族の評価を厳密回収する。
規約：辺の一致や合成端だけの一致へ弱めない。供給命題に条件付き。
使われ方：制御上側と元の全 S• Hom の core 制限の照合。 -/
theorem zeroMiddleFactorizationTetra_longHom
    (h9b : zeroMiddleFactorizationTetraSupply.{u}) (k : K _⦋0⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ (2 : Fin 4)
      (SSet.yonedaEquiv (lift (𝟙 (Δ[3] : SSet.{u + 1})) (SSet.const k) ≫
        zeroMiddleFactorizationTetra s hZ K h9b))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  have h := (zeroMiddleFactorizationTetra_spec s hZ K h9b).2.2.2 k
  let a : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌) s
  have he : lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const k) ≫
      fst (Δ[2] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm a =
        SSet.yonedaEquiv.symm a := by
    rw [← Category.assoc, lift_fst, Category.id_comp]
  have ha := (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) he).trans
    (SSet.yonedaEquiv.apply_symm_apply a)
  have hm : ∀ a b : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌, a = b →
      HEq (a.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) (b.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
    intro a b hab
    subst b
    rfl
  exact h.trans (hm _ _ ha)

end SerrePositivity.KST.Fibration
