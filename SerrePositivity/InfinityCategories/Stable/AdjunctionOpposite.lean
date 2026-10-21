module

public import SerrePositivity.InfinityCategories.F1B.KanFunctorOppositeHom
public import SerrePositivity.InfinityCategories.F1B.FunctorHomCorrespondence
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet

/-- 反転 Hom 全単射は、同じ標的関手での後合成に両立する。 -/
lemma functorOppositeHomEquiv_postcomp {A D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (J : D ⟶ E) {F G : A ⟶ D} (α : FunctorHom F G) :
    F1B.kanFunctorOppositeHomEquiv (F ≫ J) (G ≫ J)
      ((hoFunctor.map ((ihom A).map J)).toFunctor.map α) =
    (hoFunctor.map ((ihom A.op).map (opFunctor.map J))).toFunctor.map
      (F1B.kanFunctorOppositeHomEquiv F G α) := by
  have h := functorHomHomotopy_hom α
  rw [← h, ← functorHomotopyPostcomp_hom, F1B.kanFunctorOppositeHomEquiv_homotopy,
    F1B.kanFunctorOppositeHomEquiv_homotopy, ← functorHomotopyPostcomp_hom]
  congr 1

/-- 反対側の随伴から、元の全パラメータ h Fun の Hom 全単射を作る。 -/
def qcatAdjunctionOppositeHomEquiv {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y) :
    FunctorHom (U ≫ F) V ≃ FunctorHom U (V ≫ G) := by
  have e₂ : FunctorHom (opFunctor.map (V ≫ G)) (opFunctor.map U) ≃
      FunctorHom (opFunctor.map V) (opFunctor.map (U ≫ F)) := by
    simpa only [opFunctor.map_comp] using a.homEquiv (opFunctor.map V) (opFunctor.map U)
  exact (F1B.kanFunctorOppositeHomEquiv (U ≫ F) V).trans
    (e₂.symm.trans (F1B.kanFunctorOppositeHomEquiv U (V ≫ G)).symm)

/-- 元の Hom 対応を反転すると、反対側の adjunct の逆になる。 -/
lemma qcatAdjunctionOppositeHomEquiv_spec
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y)
    (α : FunctorHom (U ≫ F) V) :
    F1B.kanFunctorOppositeHomEquiv U (V ≫ G) (qcatAdjunctionOppositeHomEquiv a U V α) =
      (a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
        (F1B.kanFunctorOppositeHomEquiv (U ≫ F) V α) := by
  simp only [qcatAdjunctionOppositeHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- 元の Hom 対応は、終域側の二胞体での後合成に自然。 -/
lemma qcatAdjunctionOppositeHomEquiv_naturality_right
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] {U : A ⟶ X} {V V' : A ⟶ Y}
    (α : FunctorHom (U ≫ F) V) (β : FunctorHom V V') :
    qcatAdjunctionOppositeHomEquiv a U V' (α ≫ β) =
      qcatAdjunctionOppositeHomEquiv a U V α ≫
        (hoFunctor.map ((ihom A).map G)).toFunctor.map β := by
  apply (F1B.kanFunctorOppositeHomEquiv U (V' ≫ G)).injective
  rw [qcatAdjunctionOppositeHomEquiv_spec, F1B.kanFunctorOppositeHomEquiv_comp,
    F1B.kanFunctorOppositeHomEquiv_comp, functorOppositeHomEquiv_postcomp,
    qcatAdjunctionOppositeHomEquiv_spec]
  apply (a.homEquiv (opFunctor.map V') (opFunctor.map U)).injective
  rw [Equiv.apply_symm_apply]
  have h := (QCatFunctorHomCorrespondence.ofAdjunction a).naturality_left
    (F1B.kanFunctorOppositeHomEquiv V V' β)
    ((a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
      (F1B.kanFunctorOppositeHomEquiv (U ≫ F) V α))
  simpa only [QCatFunctorHomCorrespondence.ofAdjunction, Equiv.apply_symm_apply] using h.symm

/-- 元の Hom 対応は、始域側の二胞体での前合成に自然。 -/
lemma qcatAdjunctionOppositeHomEquiv_naturality_left
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] {U U' : A ⟶ X} {V : A ⟶ Y}
    (γ : FunctorHom U' U) (α : FunctorHom (U ≫ F) V) :
    qcatAdjunctionOppositeHomEquiv a U' V
      ((hoFunctor.map ((ihom A).map F)).toFunctor.map γ ≫ α) =
      γ ≫ qcatAdjunctionOppositeHomEquiv a U V α := by
  apply (F1B.kanFunctorOppositeHomEquiv U' (V ≫ G)).injective
  let γF : FunctorHom (U' ≫ F) (U ≫ F) :=
    (hoFunctor.map ((ihom A).map F)).toFunctor.map γ
  have hc := F1B.kanFunctorOppositeHomEquiv_comp γF α
  have hp := functorOppositeHomEquiv_postcomp F γ
  rw [qcatAdjunctionOppositeHomEquiv_spec, hc,
    F1B.kanFunctorOppositeHomEquiv_comp, hp, qcatAdjunctionOppositeHomEquiv_spec]
  apply (a.homEquiv (opFunctor.map V) (opFunctor.map U')).injective
  rw [Equiv.apply_symm_apply]
  have h := (QCatFunctorHomCorrespondence.ofAdjunction a).naturality_right
    ((a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
      (F1B.kanFunctorOppositeHomEquiv (U ≫ F) V α))
    (F1B.kanFunctorOppositeHomEquiv U' U γ)
  simpa only [QCatFunctorHomCorrespondence.ofAdjunction, Equiv.apply_symm_apply] using h.symm

/-- 元の Hom 対応は、任意の quasicategory パラメータの前合成に自然。 -/
lemma qcatAdjunctionOppositeHomEquiv_precomp
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (i : A ⟶ B) (U : B ⟶ X) (V : B ⟶ Y) (α : FunctorHom (U ≫ F) V) :
    qcatAdjunctionOppositeHomEquiv a (i ≫ U) (i ≫ V)
      ((hoFunctor.map ((pre i).app Y)).toFunctor.map α) =
    (hoFunctor.map ((pre i).app X)).toFunctor.map (qcatAdjunctionOppositeHomEquiv a U V α) := by
  apply (F1B.kanFunctorOppositeHomEquiv (i ≫ U) ((i ≫ V) ≫ G)).injective
  have hα := F1B.kanFunctorOppositeHomEquiv_precomp i α
  have hβ := F1B.kanFunctorOppositeHomEquiv_precomp i
    (qcatAdjunctionOppositeHomEquiv a U V α)
  change F1B.kanFunctorOppositeHomEquiv ((i ≫ U) ≫ F) (i ≫ V)
    ((hoFunctor.map ((pre i).app Y)).toFunctor.map α) = _ at hα
  change F1B.kanFunctorOppositeHomEquiv (i ≫ U) ((i ≫ V) ≫ G)
    ((hoFunctor.map ((pre i).app X)).toFunctor.map
      (qcatAdjunctionOppositeHomEquiv a U V α)) = _ at hβ
  rw [qcatAdjunctionOppositeHomEquiv_spec, hα, hβ,
    qcatAdjunctionOppositeHomEquiv_spec]
  apply (a.homEquiv (opFunctor.map (i ≫ V)) (opFunctor.map (i ≫ U))).injective
  rw [Equiv.apply_symm_apply]
  have h := (QCatFunctorHomCorrespondence.ofAdjunction a).precomp (opFunctor.map i)
    (opFunctor.map V) (opFunctor.map U)
    ((a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
      (F1B.kanFunctorOppositeHomEquiv (U ≫ F) V α))
  change (hoFunctor.map ((pre (opFunctor.map i)).app Y.op)).toFunctor.map
      (F1B.kanFunctorOppositeHomEquiv (U ≫ F) V α) =
    a.homEquiv (opFunctor.map i ≫ opFunctor.map V) (opFunctor.map i ≫ opFunctor.map U)
      ((hoFunctor.map ((pre (opFunctor.map i)).app X.op)).toFunctor.map
        ((a.homEquiv (opFunctor.map V) (opFunctor.map U)).symm
          (F1B.kanFunctorOppositeHomEquiv (U ≫ F) V α)))
  simpa only [QCatFunctorHomCorrespondence.ofAdjunction, Equiv.apply_symm_apply,
    opFunctor.map_comp] using h.symm

/-- 反対側の随伴を、全関手と両三角恒等式を保って元の向きへ戻す。 -/
def qcatAdjunctionOfOpposite {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction (opFunctor.map G) (opFunctor.map F)) : QCatAdjunction F G :=
  (show QCatFunctorHomCorrespondence F G from {
    equiv := qcatAdjunctionOppositeHomEquiv a
    naturality_right := qcatAdjunctionOppositeHomEquiv_naturality_right a
    naturality_left := qcatAdjunctionOppositeHomEquiv_naturality_left a
    precomp := qcatAdjunctionOppositeHomEquiv_precomp a }).toAdjunction

/-- 戻した随伴の adjunct は、指定した反転 Hom 対応と一致する。 -/
lemma qcatAdjunctionOfOpposite_homEquiv
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction (opFunctor.map G) (opFunctor.map F))
    {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y) :
    (qcatAdjunctionOfOpposite a).homEquiv U V = qcatAdjunctionOppositeHomEquiv a U V :=
  QCatFunctorHomCorrespondence.toAdjunction_homEquiv _ U V
end SerrePositivity.InfinityCategories
