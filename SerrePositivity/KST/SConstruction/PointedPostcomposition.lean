module
public import SerrePositivity.KST.SConstruction.Postcomposition
public import SerrePositivity.KST.SConstruction.KSpace

/-! # 既定の零対象を保つ射の K 空間写像
概要：零対象と押し出しを保ち、既定の零対象を厳密に保つ射は点つき K 空間の写像を誘導する。
方針：点つき対角、関手的 Kan 置換、loop の順に写像を送る。
規約：厳密な基点保存条件を明示し、一般の射の基点比較とは区別する。
使われ方：BGT §7 の反復構成と dg 関手の K 写像の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：選ばれた零対象の頂点を厳密に保つという条件。
方針：零次の成分の等号で表す。
規約：単に零対象を零対象へ送る条件より強い。使われ方：点つきの厳密な写像。 -/
def PreservesChosenZero {C D : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex D] (f : C ⟶ D) : Prop :=
  f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C).vertex = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex D).vertex

/-- 概要：恒等射は既定の零対象を厳密に保つ。
方針：頂点を変えないことを使う。
規約：quasicategory 性は不要。使われ方：点つき写像の恒等法則。 -/
lemma preservesChosenZero_id (C : SSet.{u}) [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] : PreservesChosenZero (𝟙 C) := rfl

/-- 概要：既定の零対象の保存は合成で閉じる。
方針：二つの頂点の等号を順に使う。
規約：厳密等号。使われ方：点つき写像の合成法則。 -/
lemma PreservesChosenZero.comp {C D E : SSet.{u}}
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex D] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex E] {f : C ⟶ D} {g : D ⟶ E}
    (hf : PreservesChosenZero f) (hg : PreservesChosenZero g) : PreservesChosenZero (f ≫ g) :=
  (congrArg (g.app (Opposite.op ⦋0⦌)) hf).trans hg

/-- 概要：零対象と押し出しを保つ射の点つき対角実現の写像。
方針：対角写像の零図式の像を、既定の零対象の等号で基点に同定する。
規約：既定の零対象を厳密に保つことを明示する。使われ方：関手的 Kan 置換への入力。 -/
def pointedSPostcomp {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex D] (f : C ⟶ D)
    (hf : PreservesSConstructionData f) (hzero : PreservesChosenZero f) :
    pointedSRealization C ⟶ pointedSRealization D :=
  Under.homMk (diagonalSPostcomp f hf) (by
    apply (SSet.unitHomEquiv _).injective
    change (diagonalSPostcomp f hf).app (Opposite.op ⦋0⦌)
      (SSet.unitHomEquiv _ ((SSet.unitHomEquiv _).symm
        (coreSConstructionZeroVertex 0 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C).isZero))) =
      SSet.unitHomEquiv _ ((SSet.unitHomEquiv _).symm
        (coreSConstructionZeroVertex 0 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex D).vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex D).isZero))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have he := diagonalSPostcomp_zeroVertex f hf (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C).isZero
    dsimp only [PreservesChosenZero] at hzero
    refine he.trans ?_
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : D _⦋0⦌ => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z : arNerve 0 ⟶ D)) hzero)

/-- 概要：点つき対角実現の写像は恒等射を保つ。
方針：基礎射に忘れて対角の恒等法則を使う。
規約：厳密等号。使われ方：K 写像の恒等法則。 -/
lemma pointedSPostcomp_id (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    pointedSPostcomp (𝟙 C) (preservesSConstructionData_id C) (preservesChosenZero_id C) =
      𝟙 (pointedSRealization C) := by
  apply Under.UnderMorphism.ext
  exact diagonalSPostcomp_id C

/-- 概要：点つき対角実現の写像は合成を保つ。
方針：基礎射に忘れて対角の合成法則を使う。
規約：保存条件の証明には依存しない。使われ方：K 写像の合成法則。 -/
lemma pointedSPostcomp_comp {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex D] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex E]
    (f : C ⟶ D) (g : D ⟶ E) (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g)
    (hfzero : PreservesChosenZero f) (hgzero : PreservesChosenZero g) :
    pointedSPostcomp (f ≫ g) (hf.comp hg) (hfzero.comp hgzero) =
      pointedSPostcomp f hf hfzero ≫ pointedSPostcomp g hg hgzero := by
  apply Under.UnderMorphism.ext
  exact diagonalSPostcomp_comp f g hf hg

/-- 概要：既定の零対象を保つ射の Kan 実現の間の写像。
方針：点つき対角写像に L9 の関手的 Kan 置換を適用する。
規約：基点は厳密に保存する。使われ方：K 空間の loop 写像。 -/
def kanSPostcomp {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex D] (f : C ⟶ D)
    (hf : PreservesSConstructionData f) (hzero : PreservesChosenZero f) :
    kanSRealization C ⟶ kanSRealization D :=
  Spectra.PointedKanReplacement.functor.map (pointedSPostcomp f hf hzero)

/-- 概要：既定の零対象を保つ射が K 空間の間に誘導する写像。
方針：点つき対角写像を Kan 置換して loop を取る。
規約：基点保存の条件を省略しない。使われ方：反復構成と dg 関手の適用。 -/
def kSpacePostcomp {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex D] (f : C ⟶ D)
    (hf : PreservesSConstructionData f) (hzero : PreservesChosenZero f) :
    kSpace C ⟶ kSpace D :=
  (Spectra.PointedKanReplacement.functor ⋙
    PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}).map
      (pointedSPostcomp f hf hzero)

/-- 概要：K 空間の後合成写像は恒等射を保つ。
方針：点つき対角写像と二つの関手の恒等法則を使う。
規約：厳密等号。使われ方：K 空間の関手性。 -/
lemma kSpacePostcomp_id (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] :
    kSpacePostcomp (𝟙 C) (preservesSConstructionData_id C) (preservesChosenZero_id C) =
      𝟙 (kSpace C) := by
  unfold kSpacePostcomp
  rw [pointedSPostcomp_id, CategoryTheory.Functor.map_id]
  rfl

/-- 概要：K 空間の後合成写像は合成を保つ。
方針：点つき対角写像と二つの関手の合成法則を使う。
規約：厳密等号。使われ方：K 空間の関手性。 -/
lemma kSpacePostcomp_comp {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex D] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex E]
    (f : C ⟶ D) (g : D ⟶ E) (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g)
    (hfzero : PreservesChosenZero f) (hgzero : PreservesChosenZero g) :
    kSpacePostcomp (f ≫ g) (hf.comp hg) (hfzero.comp hgzero) =
      kSpacePostcomp f hf hfzero ≫ kSpacePostcomp g hg hgzero := by
  unfold kSpacePostcomp
  rw [pointedSPostcomp_comp, CategoryTheory.Functor.map_comp]

end SerrePositivity.KST.SConstruction
