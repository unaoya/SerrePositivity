module
public import SerrePositivity.KST.SConstruction.StableModels
public import SerrePositivity.KST.SConstruction.MultiSimplicial
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：指定された充満忠実な完全射の S_n 後合成も充満忠実である。
方針：全 Ar 図式の後合成の充満忠実性を、元の gapped 全部分複体へ制限する。
規約：core の本質全射性や実現の同値は結論しない。
使われ方：dense 完備化射の S• 直接比較における充満忠実性の部分。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

/-- 概要：元の完全射の充満忠実性は、全 gapped S_n で保持される。
方針：gapped 包含の充満忠実性により全 Ar 図式上の後合成へ戻す。
規約：任意の n を扱い、面や core の対象を選び直さない。
使われ方：共終性の有限 S 図式側の充満忠実性。 -/
lemma sEndofunctor_map_isFullyFaithful (n : ℕ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((sEndofunctor n).map f).val := by
  let : Quasicategory (diagramSpace n X.carrier) := by
    dsimp [diagramSpace]
    infer_instance
  let : Quasicategory (diagramSpace n Y.carrier) := by
    dsimp [diagramSpace]
    infer_instance
  let : Quasicategory (gappedSubcomplex n X.carrier).toSSet :=
    sConstruction_quasicategory n X.carrier
  let : Quasicategory (gappedSubcomplex n Y.carrier).toSSet :=
    sConstruction_quasicategory n Y.carrier
  have hiY : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (gappedSubcomplex n Y.carrier).ι :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  have hiX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (gappedSubcomplex n X.carrier).ι :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  apply hiY.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((gappedSubcomplex n X.carrier).ι ≫
    (ihom (arNerve n)).map f.val)
  exact hiX.comp (hf.postcompose (arNerve n))

/-- 概要：元の充満忠実な完全射は独立な全多次数の有限反復 S でも充満忠実。
方針：各方向の S_n 後合成の充満忠実性を反復数について帰納する。
規約：対角だけに制限せず、実現後の同値性とは区別する。
使われ方：正反復 S• の dense 比較で全方向を保つ充満忠実性。 -/
lemma multiSEndofunctor_map_isFullyFaithful (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (((multiSEndofunctor r).obj d).map f).val := by
  induction r generalizing X Y with
  | zero => exact hf
  | succ r ih =>
    exact sEndofunctor_map_isFullyFaithful (d 0).unop.len
      (((multiSEndofunctor r).obj (fun i => d i.succ)).map f)
      (ih (fun i => d i.succ) f hf)

end SerrePositivity.KST.SConstruction.Cofinality
