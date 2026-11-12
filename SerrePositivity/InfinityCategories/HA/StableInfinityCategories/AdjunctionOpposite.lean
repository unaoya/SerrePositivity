module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOppositeHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence
/-!
概要：反対圏の随伴を、元の二関手の随伴へ戻す。
方針：h Fun の反転 Hom 全単射と反対側の adjunct を合成し、全パラメータの自然性を移す。
規約：単位・余単位と両三角式を持つ quasicategory の随伴を返す。
使われ方：一般 kernel の実余単位を標準単位判定へ反転した後の随伴の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalClosed SSet

/-- 反転 Hom 全単射は、同じ標的関手での後合成に両立する。 -/
lemma functorOppositeHomEquiv_postcomp {A D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (J : D ⟶ E) {F G : A ⟶ D} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (F ≫ J) (G ≫ J)
      ((hoFunctor.map ((ihom A).map J)).toFunctor.map α) =
    (hoFunctor.map ((ihom A.op).map (opFunctor.map J))).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv F G α) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom α
  rw [← h, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_homotopy,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_homotopy, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
  congr 1

/-- 反対側の随伴から、元の全パラメータ h Fun の Hom 全単射を作る。 -/
def qcatAdjunctionOppositeHomEquiv {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ G) := by
  have e₂ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (opFunctor.map (V ≫ G)) (opFunctor.map U) ≃
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (opFunctor.map V) (opFunctor.map (U ≫ F)) := by
    simpa only [opFunctor.map_comp] using a.homEquiv (opFunctor.map V) (opFunctor.map U)
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (U ≫ F) V).trans
    (e₂.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv U (V ≫ G)).symm)

/-- 元の Hom 対応を反転すると、反対側の adjunct の逆になる。 -/
lemma qcatAdjunctionOppositeHomEquiv_spec
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv U (V ≫ G) (qcatAdjunctionOppositeHomEquiv a U V α) =
      (a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (U ≫ F) V α) := by
  simp only [qcatAdjunctionOppositeHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- 元の Hom 対応は、終域側の二胞体での後合成に自然。 -/
lemma qcatAdjunctionOppositeHomEquiv_naturality_right
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] {U : A ⟶ X} {V V' : A ⟶ Y}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V V') :
    qcatAdjunctionOppositeHomEquiv a U V' (α ≫ β) =
      qcatAdjunctionOppositeHomEquiv a U V α ≫
        (hoFunctor.map ((ihom A).map G)).toFunctor.map β := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv U (V' ≫ G)).injective
  rw [qcatAdjunctionOppositeHomEquiv_spec, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_comp,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_comp, functorOppositeHomEquiv_postcomp,
    qcatAdjunctionOppositeHomEquiv_spec]
  apply (a.homEquiv (opFunctor.map V') (opFunctor.map U)).injective
  rw [Equiv.apply_symm_apply]
  have h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.QCatFunctorHomCorrespondence.ofAdjunction a).naturality_left
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv V V' β)
    ((a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (U ≫ F) V α))
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.QCatFunctorHomCorrespondence.ofAdjunction, Equiv.apply_symm_apply] using h.symm

/-- 元の Hom 対応は、始域側の二胞体での前合成に自然。 -/
lemma qcatAdjunctionOppositeHomEquiv_naturality_left
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] {U U' : A ⟶ X} {V : A ⟶ Y}
    (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' U) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) :
    qcatAdjunctionOppositeHomEquiv a U' V
      ((hoFunctor.map ((ihom A).map F)).toFunctor.map γ ≫ α) =
      γ ≫ qcatAdjunctionOppositeHomEquiv a U V α := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv U' (V ≫ G)).injective
  let γF : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U' ≫ F) (U ≫ F) :=
    (hoFunctor.map ((ihom A).map F)).toFunctor.map γ
  have hc := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_comp γF α
  have hp := functorOppositeHomEquiv_postcomp F γ
  rw [qcatAdjunctionOppositeHomEquiv_spec, hc,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_comp, hp, qcatAdjunctionOppositeHomEquiv_spec]
  apply (a.homEquiv (opFunctor.map V) (opFunctor.map U')).injective
  rw [Equiv.apply_symm_apply]
  have h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.QCatFunctorHomCorrespondence.ofAdjunction a).naturality_right
    ((a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (U ≫ F) V α))
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv U' U γ)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.QCatFunctorHomCorrespondence.ofAdjunction, Equiv.apply_symm_apply] using h.symm

/-- 元の Hom 対応は、任意の quasicategory パラメータの前合成に自然。 -/
lemma qcatAdjunctionOppositeHomEquiv_precomp
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (i : A ⟶ B) (U : B ⟶ X) (V : B ⟶ Y) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) :
    qcatAdjunctionOppositeHomEquiv a (i ≫ U) (i ≫ V)
      ((hoFunctor.map ((pre i).app Y)).toFunctor.map α) =
    (hoFunctor.map ((pre i).app X)).toFunctor.map (qcatAdjunctionOppositeHomEquiv a U V α) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (i ≫ U) ((i ≫ V) ≫ G)).injective
  have hα := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_precomp i α
  have hβ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_precomp i
    (qcatAdjunctionOppositeHomEquiv a U V α)
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv ((i ≫ U) ≫ F) (i ≫ V)
    ((hoFunctor.map ((pre i).app Y)).toFunctor.map α) = _ at hα
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (i ≫ U) ((i ≫ V) ≫ G)
    ((hoFunctor.map ((pre i).app X)).toFunctor.map
      (qcatAdjunctionOppositeHomEquiv a U V α)) = _ at hβ
  rw [qcatAdjunctionOppositeHomEquiv_spec, hα, hβ,
    qcatAdjunctionOppositeHomEquiv_spec]
  apply (a.homEquiv (opFunctor.map (i ≫ V)) (opFunctor.map (i ≫ U))).injective
  rw [Equiv.apply_symm_apply]
  have h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.QCatFunctorHomCorrespondence.ofAdjunction a).precomp (opFunctor.map i)
    (opFunctor.map V) (opFunctor.map U)
    ((a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (U ≫ F) V α))
  change (hoFunctor.map ((pre (opFunctor.map i)).app Y.op)).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (U ≫ F) V α) =
    a.homEquiv (opFunctor.map i ≫ opFunctor.map V) (opFunctor.map i ≫ opFunctor.map U)
      ((hoFunctor.map ((pre (opFunctor.map i)).app X.op)).toFunctor.map
        ((a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
          (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (U ≫ F) V α)))
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.QCatFunctorHomCorrespondence.ofAdjunction, Equiv.apply_symm_apply,
    opFunctor.map_comp] using h.symm

/-- 反対側の随伴を、全関手と両三角恒等式を保って元の向きへ戻す。 -/
def qcatAdjunctionOfOpposite {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (opFunctor.map G) (opFunctor.map F)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G :=
  (show _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.QCatFunctorHomCorrespondence F G from {
    equiv := qcatAdjunctionOppositeHomEquiv a
    naturality_right := qcatAdjunctionOppositeHomEquiv_naturality_right a
    naturality_left := qcatAdjunctionOppositeHomEquiv_naturality_left a
    precomp := qcatAdjunctionOppositeHomEquiv_precomp a }).toAdjunction

/-- 戻した随伴の adjunct は、指定した反転 Hom 対応と一致する。 -/
lemma qcatAdjunctionOfOpposite_homEquiv
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y) :
    (qcatAdjunctionOfOpposite a).homEquiv U V = qcatAdjunctionOppositeHomEquiv a U V :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.QCatFunctorHomCorrespondence.toAdjunction_homEquiv _ U V
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
