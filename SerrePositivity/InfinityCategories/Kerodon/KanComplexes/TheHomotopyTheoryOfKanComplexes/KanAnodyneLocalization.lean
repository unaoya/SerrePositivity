module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection

/-!
概要：Kan 複体間の実際の同値と、anodyne 局所化での可逆性を照合する。
方針：区間ホモトピー類を関手空間の連結成分へ送り、二つの Kan 標的テストから逆射を回収する。
規約：値宇宙のモデル構造を公開仮定にせず、既存の Kan 充填性と局所化だけを入力にする。
使われ方：二重単体図式の対角の局所化可逆性を、元の Kan 写像空間の実際の同値へ戻す。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- Kan 値の区間ホモトピー類を、元の関手空間の連結成分へ送る。 -/
def anodyneHomClassToPiZero {A Z : SSet.{u}} [KanComplex Z] :
    HomotopyClasses.obj A Z → SSet.π₀ ((ihom A).obj Z) :=
  Quot.lift (fun f ↦ SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (fun f g h ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy f g).mpr h)

private lemma native_terminal_rlp (Z : SSet.{u}) [KanComplex Z] :
    SSet.modelCategoryQuillen.J.rlp (terminal.from Z) := by
  have : HomotopicalAlgebra.IsFibrant Z :=
    (HomotopicalAlgebra.isFibrant_iff Z).mp inferInstance
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance

/-- Kan 複体間で局所化可逆な元の射は、実際のホモトピー逆を持つ。 -/
lemma isQCatEquivalence_of_anodyneQ_isIso {A B : SSet.{u}} [KanComplex A] [KanComplex B]
    (f : A ⟶ B) (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f := by
  have ht := KanTestDetection.tests_of_anodyneQ_isIso f hf
  obtain ⟨a, ha⟩ := (ht A (native_terminal_rlp A)).surjective (HomotopyClasses.mk (𝟙 A))
  obtain ⟨g, rfl⟩ := Quot.exists_rep a
  change HomotopyClasses.mk (f ≫ g) = HomotopyClasses.mk (𝟙 A) at ha
  have hb : HomotopyClasses.mk (g ≫ f) = HomotopyClasses.mk (𝟙 B) := by
    apply (ht B (native_terminal_rlp B)).injective
    change HomotopyClasses.mk (f ≫ (g ≫ f)) = HomotopyClasses.mk (f ≫ 𝟙 B)
    have h := congrArg (HomotopyClasses.post f) ha
    change HomotopyClasses.mk ((f ≫ g) ≫ f) = HomotopyClasses.mk ((𝟙 A) ≫ f) at h
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using h
  have hA : SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ g)) = SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 A)) :=
    congrArg (anodyneHomClassToPiZero (A := A) (Z := A)) ha
  have hB : SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ f)) = SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 B)) :=
    congrArg (anodyneHomClassToPiZero (A := B) (Z := B)) hb
  exact (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f from
    ⟨g, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp hA,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp hB⟩).isQCatEquivalence

/-- 実際の Kan 同値は、anodyne 局所化で可逆となる。 -/
lemma IsQCatEquivalence.anodyneQ_isIso {A B : SSet.{u}} [KanComplex A] [KanComplex B]
    {f : A ⟶ B} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) : IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := hf.isSimplicialHomotopyEquivalence
  let Q := AnodyneHomotopy.anodyneQ
  have hQ := Localization.inverts Q SSet.anodyneExtensions
  let e : Q.obj A ≅ Q.obj B :=
    { hom := Q.map f
      inv := Q.map g
      hom_inv_id := by
        rw [← Q.map_comp]
        exact (AnodyneHomotopy.map_homotopy_eq Q hQ H).trans (Q.map_id A)
      inv_hom_id := by
        rw [← Q.map_comp]
        exact (AnodyneHomotopy.map_homotopy_eq Q hQ K).trans (Q.map_id B) }
  exact e.isIso_hom

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
