module
public import SerrePositivity.KST.SConstruction.Cofinality.DiagramImage
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：有限 S 図式の全族回収を、指定された境界図式と比較する。
方針：元の全族比較と指定境界比較を合成し、同じ S_n 射の充満忠実性で戻す。
規約：境界上の比較同型を保持するが、境界図式の厳密な等号による延長とは区別する。
使われ方：相対 S• 比較で指定境界を保つ回収の準備。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の全族比較と指定境界比較から同じ像内の境界比較を取り出す。
方針：指定された二同型を合成し、結合則だけで元の両端へ輸送する。
規約：境界比較の代表を新しく選ばない。
使われ方：充満忠実性による元の境界図式への反映。 -/
def sBoundaryImageIso {n : ℕ} {L K : SSet.{u}} {X Y : StableModel.{u}}
    (f : X ⟶ Y) (i : L ⟶ K) (G : K ⟶ sConstruction n X.carrier)
    (g : L ⟶ sConstruction n X.carrier) (F : K ⟶ sConstruction n Y.carrier)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ ((sEndofunctor n).map f).val) F)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ ((sEndofunctor n).map f).val) (i ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((i ≫ G) ≫ ((sEndofunctor n).map f).val)
      (g ≫ ((sEndofunctor n).map f).val) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((e.precomp i) ≪≫ b.symm) (Category.assoc _ _ _).symm rfl

/-- 概要：元の全族回収を指定された始域の境界図式と同じ始域内で比較する。
方針：指定像内比較を同じ S_n 射の充満忠実性で反映する。
規約：厳密な境界等号や相対ホモトピー延長は主張しない。
使われ方：同じ境界の相対比較を構成する入口。 -/
def sBoundaryRecoveryIso {n : ℕ} {L K : SSet.{u}} {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val) (i : L ⟶ K)
    (G : K ⟶ sConstruction n X.carrier) (g : L ⟶ sConstruction n X.carrier)
    (F : K ⟶ sConstruction n Y.carrier)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ ((sEndofunctor n).map f).val) F)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ ((sEndofunctor n).map f).val) (i ≫ F)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ G) g :=
  (sEndofunctor_map_isFullyFaithful n f hf).preimageFunctorIso (sBoundaryImageIso f i G g F e b)

/-- 概要：元の境界比較を反映してから同じ S_n 射へ写すと、指定した像内比較を回収する。
方針：全関手圏のホモトピー圏の充満忠実性の逆像公式を使う。
規約：指定比較の等号を保ち、存在だけに弱めない。
使われ方：元の境界と全族比較を相対的に照合する。 -/
lemma sBoundaryRecoveryIso_postcomp {n : ℕ} {L K : SSet.{u}} {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val) (i : L ⟶ K)
    (G : K ⟶ sConstruction n X.carrier) (g : L ⟶ sConstruction n X.carrier)
    (F : K ⟶ sConstruction n Y.carrier)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ ((sEndofunctor n).map f).val) F)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ ((sEndofunctor n).map f).val) (i ≫ F)) :
    (sBoundaryRecoveryIso f hf i G g F e b).postcomp ((sEndofunctor n).map f).val =
      sBoundaryImageIso f i G g F e b := by
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso
    (sBoundaryRecoveryIso f hf i G g F e b) ((sEndofunctor n).map f).val).trans ?_
  apply Iso.ext
  exact ((sEndofunctor_map_isFullyFaithful n f hf).postcompose L).toHoFullyFaithful.map_preimage _

end SerrePositivity.KST.SConstruction.Cofinality
