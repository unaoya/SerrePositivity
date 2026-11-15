module
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOppositeHom
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：同じ関手同型の反転と前合成・端点輸送の両立。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 反転した頂点同型の逆射は、元の順射の反転 Hom 対応による像。 -/
lemma sameVertexIso_op_inv {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : VertexIso x y) :
    e.op.inv = homotopyCategoryOpHomEquiv x y e.hom := by
  let a := (homotopyCategory_homMk_surjective x y e.hom).choose
  have ha : SSet.Truncated.HomotopyCategory.homMk a = e.hom :=
    (homotopyCategory_homMk_surjective x y e.hom).choose_spec
  change SSet.Truncated.HomotopyCategory.homMk
    (SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp a) = _
  rw [← homotopyCategoryOpHomEquiv_homMk, ha]

private lemma sameEqMp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (b : γ) :
    HEq (Eq.mp h a) b ↔ HEq a b := by cases h; rfl

/-- 反転した同じ関手同型は、内部 Hom の反転による元の像と端点輸送を除いて一致する。 -/
lemma sameFunctorIso_op_heq {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    HEq e.op (VertexIso.map (VertexIso.op e)
      (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom) := by
  unfold SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.FunctorIso.op
  simp only [sameEqMp_heq_iff]
  rfl

/-- 端点の等式で共役した同じ同型は、元の値と HEq で一致する。 -/
lemma sameVertexIso_conjugate_heq {Z : SSet.{u}} {a b a' b' : Z _⦋0⦌}
    (e : VertexIso a b) (ha : a = a') (hb : b = b') :
    HEq ((eqToIso (congrArg HomotopyCategory.mk ha)).symm ≪≫ e ≪≫
        eqToIso (congrArg HomotopyCategory.mk hb)) e := by
  cases ha
  cases hb
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  rfl

/-- 同じ関手同型の反転は、内部 Hom の像を同じ端点等式で共役したもの。 -/
lemma sameFunctorIso_op_conjugate {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    e.op = (eqToIso (congrArg HomotopyCategory.mk
      (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex f))).symm ≪≫
      VertexIso.map (VertexIso.op e)
        (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex g)) := by
  exact eq_of_heq ((sameFunctorIso_op_heq e).trans
    (sameVertexIso_conjugate_heq (VertexIso.map (VertexIso.op e)
      (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom)
      (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex f)
      (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex g)).symm)

/-- 同じ関手同型の反転の逆射を、元の順射の反転 Hom 対応として回収する。 -/
lemma sameFunctorIso_op_inv {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    e.op.inv = functorOppositeHomEquiv f g e.hom := by
  rw [sameFunctorIso_op_conjugate]
  simp only [Iso.trans_inv, Iso.symm_inv, VertexIso.map, Functor.mapIso_inv,
    Category.assoc]
  rw [sameVertexIso_op_inv]
  simp only [functorOppositeHomEquiv, Equiv.trans_apply, Equiv.coe_ofBijective,
    Iso.homCongr_apply]

/-- 同じ関手同型の前合成は、ホモトピー圏で元の逆射を写したものを逆射に持つ。 -/
lemma sameFunctorIso_precomp_inv {A X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (p : A ⟶ X) :
    (e.precomp p).inv = (SSet.mapHomotopyCategory ((pre p).app Y)).map e.inv := by
  rfl

/-- 同じ関手同型を制限して反転する値と、反転して同じ入力へ制限する値は一致する。 -/
lemma sameFunctorIso_op_precomp {A X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) (p : A ⟶ X) :
    HEq (e.precomp p).op (e.op.precomp (SSet.opFunctor.map p)) := by
  apply heq_of_eq
  apply Iso.ext_inv
  rw [sameFunctorIso_op_inv, sameFunctorIso_precomp_inv, sameFunctorIso_op_inv]
  have h := functorOppositeHomEquiv_precomp p e.hom
  change functorOppositeHomEquiv (p ≫ f) (p ≫ g)
    ((SSet.mapHomotopyCategory ((pre p).app Y)).map e.hom) =
      (SSet.mapHomotopyCategory ((pre (SSet.opFunctor.map p)).app Y.op)).map
        (functorOppositeHomEquiv f g e.hom) at h
  simpa only [functorIso_precomp_hom] using h

/-- 端点と値の照合は、同じ入力による前合成後も保たれる。 -/
lemma sameFunctorIso_precomp_of_heq {K X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (he : HEq e e') (p : K ⟶ X) : HEq (e.precomp p) (e'.precomp p) := by
  subst f' g'
  cases he
  rfl

/-- 端点と値の照合は、同じ関手同型を反転した後も保たれる。 -/
lemma sameFunctorIso_op_of_heq {X Y : SSet.{u}} [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') : HEq e.op e'.op := by
  subst f' g'
  cases he
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
