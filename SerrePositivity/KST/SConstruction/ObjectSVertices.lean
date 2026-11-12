module
public import SerrePositivity.KST.SConstruction.ObjectSConstruction

/-! # object S の単体と実際の gapped 図式の対応
概要：object S の零単体表示を gapped な実際の射へ戻し、添字と入力の射への作用を照合する。
方針：内部 Hom の頂点同値と全部分複体の包含を使う。
規約：元の全 gapped 図式の模型を保持する。使われ方：object S の単体ホモトピーの計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：gapped な実際の図式を S_n の頂点に戻す。
方針：内部 Hom の頂点と全部分複体の零次元条件。
規約：選択は加えない。使われ方：object S の候補単体の構成。 -/
def gappedObjectVertex {n : ℕ} {C : SSet.{u}} (F : arNerve n ⟶ C) (hF : IsGapped F) :
    (sConstruction n C) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C F))
    rw [Equiv.symm_apply_apply]
    exact hF⟩

/-- 概要：頂点に戻してから取り出すと元の実際の図式。
方針：内部 Hom の頂点同値の逆律。
規約：厳密等号。使われ方：単体ホモトピーの自然性。 -/
lemma gappedDiagram_gappedObjectVertex {n : ℕ} {C : SSet.{u}}
    (F : arNerve n ⟶ C) (hF : IsGapped F) : gappedDiagram (gappedObjectVertex F hF) = F :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm_apply_apply F

/-- 概要：実際の図式への対応は単射。
方針：頂点同値の逆の単射性と部分型の外延性。
規約：gapped 条件の証明の違いは忘れる。使われ方：object S の単体の等号の判定。 -/
lemma gappedDiagram_injective {n : ℕ} {C : SSet.{u}} :
    Function.Injective (@gappedDiagram n C) := by
  intro v w h
  exact Subtype.ext ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm.injective h)

/-- 概要：S の添字制限は実際の Ar 図式の前合成。
方針：内部 Hom の前合成を関手頂点の同値で読む。
規約：全ての順序写像に共通。使われ方：ホモトピーの面・退化の式。 -/
lemma gappedDiagram_sMap {m n : ℕ} {C : SSet.{u}} (θ : Fin (m + 1) →o Fin (n + 1))
    (v : (sConstruction n C) _⦋0⦌) :
    gappedDiagram ((sMap C θ).app (Opposite.op ⦋0⦌) v) = arNerveMap θ ≫ gappedDiagram v := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm
    (((MonoidalClosed.pre (arNerveMap θ)).app C).app (Opposite.op ⦋0⦌) v.val) = _
  rw [← hv]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C (arNerveMap θ ≫ gappedDiagram v)) = _
  exact Equiv.symm_apply_apply _ _

/-- 概要：object S の単体作用は Ar 図式の前合成。
方針：S• の零次数評価の定義と添字制限の式。
規約：始域と終域は任意の単体次数。使われ方：object S の自然性の直接の式。 -/
lemma gappedDiagram_objectS_map {C : SSet.{u}} {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (v : (objectSConstruction C).obj n) :
    gappedDiagram ((objectSConstruction C).map α v) =
      arNerveMap α.unop.toOrderHom ≫ gappedDiagram v := gappedDiagram_sMap _ v

/-- 概要：cofiber 保存射による S_n の後合成は実際の図式の後合成。
方針：内部 Hom の後合成を頂点同値で読む。
規約：標的の quasicategory 性のみ。使われ方：object S の入力の射への作用。 -/
lemma gappedDiagram_sPostcompCofiber {n : ℕ} {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) (v : (sConstruction n C) _⦋0⦌) :
    gappedDiagram ((sPostcompCofiber n f hf).app (Opposite.op ⦋0⦌) v) = gappedDiagram v ≫ f := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sPostcompCofiber_ι n f hf) (Opposite.op ⦋0⦌)) v
  change ((sPostcompCofiber n f hf).app (Opposite.op ⦋0⦌) v).val =
    (((ihom (arNerve n)).map f).app (Opposite.op ⦋0⦌) v.val) at he
  dsimp only [gappedDiagram]
  rw [he]
  rw [← hv]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D (gappedDiagram v ≫ f)) = _
  exact Equiv.symm_apply_apply _ _

/-- 概要：object S の入力の射への作用は実際の図式の後合成。
方針：cofiber 保存型の後合成の頂点表示を適用する。
規約：元の object S 関手の射を照合する。使われ方：ホモトピーの両端の回収。 -/
lemma gappedDiagram_objectSFunctor_map {X Y : StableModel.{u}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (v : (objectSConstruction X.carrier).obj n) :
    gappedDiagram ((objectSConstructionFunctor.map f).app n v) = gappedDiagram v ≫ f.val :=
  gappedDiagram_sPostcompCofiber f.val f.property v

end SerrePositivity.KST.SConstruction
