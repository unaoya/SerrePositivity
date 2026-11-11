module
public import SerrePositivity.KST.Fibration.ZeroMiddleFactorizationTetra

/-!
概要：供給された因子分解族を、元の三面を固定する実充填比較へ接続する。
方針：三面の厳密回収から元のホーン全体を回収し、その同じ fiber 内で先に比較する。
規約：Ind-S (9b) に条件付きで、境界一致から任意の充填の存在は推論しない。
使われ方：K-6 c4 の制御上側と既存上側・元の native 二胞体の全族比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1})

/-- 概要：同じ因子分解条件の実族は元の三面のホーン全体を厳密回収する。
方針：積の閉構造で転置し、元の三面の余極限性を使う。
規約：元の零中間二胞体に限る利用側の照合であり、一般充填 API ではない。
使われ方：構成済み F を元の固定三面 fiber へ置く。 -/
theorem zeroMiddleFactorizationTetraCondition_horn
    (F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : zeroMiddleFactorizationTetraCondition s hZ K F) :
    ((horn 3 (2 : Fin 4)).ι ▷ K) ≫ F =
      fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ := by
  apply (cancel_epi (β_ K (horn 3 (2 : Fin 4) : SSet.{u+1})).hom).mp
  apply curry_injective
  apply horn.hom_ext'
  intro j hj
  rw [← curry_natural_left, ← curry_natural_left]
  congr 1
  simp only [← Category.assoc, BraidedCategory.braiding_naturality_right]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι,
    ← Category.assoc, whiskerRight_fst, Category.assoc]
  fin_cases j
  · exact hF.1.trans (congrArg (fun t => fst (Δ[2] : SSet.{u+1}) K ≫ t)
      (by symm; apply horn₃₂.ι₀_desc))
  · exact hF.2.1.trans (congrArg (fun t => fst (Δ[2] : SSet.{u+1}) K ≫ t)
      (zeroMiddleFullSKanHorn_original s hZ).symm)
  · exact False.elim (hj rfl)
  · exact hF.2.2.1.trans (congrArg (fun t => fst (Δ[2] : SSet.{u+1}) K ≫ t)
      (by symm; apply horn₃₂.ι₃_desc))

variable (h9b : zeroMiddleFactorizationTetraSupply.{u})

/-- 概要：供給命題から得た同じ実因子分解族は元のホーン全体を保持する。
方針：同じ族の三面回収をホーン回収へ渡す。
規約：存在は Ind-S (9b) に条件付き。
使われ方：既存充填と比較する同じ実 fiber の入力。 -/
theorem zeroMiddleFactorizationTetra_horn :
    ((horn 3 (2 : Fin 4)).ι ▷ K) ≫ zeroMiddleFactorizationTetra s hZ K h9b =
      fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ :=
  zeroMiddleFactorizationTetraCondition_horn s hZ K _
    (zeroMiddleFactorizationTetra_spec s hZ K h9b)

/-- 概要：同じ実因子分解族は元の既存充填と固定三面 fiber 内で同型。
方針：ホーン回収後に限り、構成済みの同じ実族を既存の比較へ渡す。
規約：供給命題に条件付きで、既存充填は保持する。
使われ方：制御上側を使う前に必要な全族の比較。 -/
def zeroMiddleFactorizationFixedHornComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (zeroMiddleFixedHornOriginalFamilyVertex s hZ K)
      (zeroMiddleFixedHornFamilyVertex s hZ K
        (zeroMiddleFactorizationTetra s hZ K h9b)
        (zeroMiddleFactorizationTetra_horn s hZ K h9b)) :=
  zeroMiddleFixedHornFamilyComparison s hZ K _ (zeroMiddleFactorizationTetra_horn s hZ K h9b)

/-- 概要：元の既存上側と制御上側を同じ実全族で比較する。
方針：固定三面 fiber 内の比較から上側へ制限する既存の実ホモトピーを使う。
規約：全境界固定の同じ比較を保持し、長 Hom の照合は因子分解条件に残す。
使われ方：K-6 c4 の既存上側を保つ条件付きの全族同型。 -/
def zeroMiddleFactorizationUpperIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫
      fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ)
    ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫ zeroMiddleFactorizationTetra s hZ K h9b) :=
  zeroMiddleFixedHornRelativeUpperFamilyIso s hZ K _
    (zeroMiddleFactorizationTetra_horn s hZ K h9b)

/-- 概要：同じ制御上側から元の指定 native 二胞体の全族へ戻る実同型。
方針：同じ実三単体族とその元のホーン回収を実三角柱比較へ渡す。
規約：共有対角と元の可逆縦辺を保持する同じ実ホモトピーから得る。
使われ方：K-6 c4 から元の Verdier 上側への受け渡し。 -/
def zeroMiddleFactorizationPrismIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫ zeroMiddleFactorizationTetra s hZ K h9b)
    (fst (Δ[2] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s)) :=
  zeroMiddleControlledPrismFamilyIso s hZ K _
    (zeroMiddleFactorizationTetra_horn s hZ K h9b)

end SerrePositivity.KST.Fibration
