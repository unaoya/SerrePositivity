module
public import SerrePositivity.KST.SConstruction.CoherentDiagramOverEdges
public import SerrePositivity.KST.SConstruction.KanCospanPastingChoices
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation

/-! # 全パラメーターの over 族の二脚の貼り合わせ
概要：重み付き自然族の二脚を、全パラメーターで同時に貼る。
方針：パラメーターを内部 Hom へ移し、同じ終点への二辺のホーンを充填する。
規約：パラメーターの有限性・Kan 性・可縮性は要求しない。
使われ方：組み立ての全選択空間上の二脚と高次の相対補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed BraidedCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 重み付きの全パラメーターの自然族を、内部 Hom 値の自然族へ移す。 -/
def diagramFamilyTranspose {I : Type u} [SmallCategory I]
    {W D : I ⥤ SSet.{u}} {P : SSet.{u}}
    (s : W ⊗ (Functor.const I).obj P ⟶ D) : W ⟶ D ⋙ ihom P where
  app i := curry ((β_ P (W.obj i)).hom ≫ s.app i)
  naturality i j h := by
    change W.map h ≫ curry ((β_ P (W.obj j)).hom ≫ s.app j) =
      curry ((β_ P (W.obj i)).hom ≫ s.app i) ≫ (ihom P).map (D.map h)
    rw [← curry_natural_left, ← curry_natural_right]
    apply congrArg curry
    rw [← Category.assoc, braiding_naturality_right, Category.assoc]
    exact congrArg ((β_ P (W.obj i)).hom ≫ ·) (s.naturality h)

/-- 全選択空間をパラメーターとした普遍 over 族。 -/
def diagramUniversalFamily {I : Type u} [SmallCategory I] (D : I ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ D ⋙ ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D) :=
  diagramFamilyTranspose (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D)))

/-- 普遍族を選択空間の頂点で評価すると、同じ頂点の元の over 族を厳密に回収する。 -/
lemma diagramUniversalFamily_evaluation {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D) _⦋0⦌) (i : I) :
    (diagramUniversalFamily D).app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v = (diagramSelectionAt D v).app i := by
  let a := (SSet.unitHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D)).symm v
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.curry_evaluateFunctorAt_unitHomEquiv
    ((β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)).hom ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D i)) a
  rw [Equiv.apply_symm_apply] at he
  change curry ((β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)).hom ≫
      uncurry ((𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D i)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v =
    (ρ_ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)).inv ≫
      uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D i)
  rw [Category.id_comp, he, uncurry_natural_left]
  simp only [← Category.assoc]
  apply congrArg (· ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D i))
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro w
  rfl

/-- 普遍族の比較辺を評価すると、同じ選択の元の比較辺の一単体になる。 -/
lemma diagramUniversalFamily_edge_evaluation {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D) _⦋0⦌)
    {i j : I} (h : i ⟶ j) :
    ((diagramSelectionEdge (diagramUniversalFamily D) h).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)).edge =
      (diagramSelectionEdge (diagramSelectionAt D v) h).edge := by
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (diagramUniversalFamily_evaluation D v j) (Opposite.op ⦋1⦌))
    (CategoryTheory.nerve.edgeMk (diagramSelectionOverArrow h)).edge
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v).app (Opposite.op ⦋1⦌)
    (diagramSelectionEdge (diagramUniversalFamily D) h).edge = _
  rw [diagramSelectionEdge_edge, diagramSelectionEdge_edge]
  exact he

/-- 普遍族の比較辺の評価は、恒等成分を元の表示へ戻した辺も回収する。 -/
lemma diagramUniversalFamily_transportEdge_evaluation {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D) _⦋0⦌)
    {i j : I} (h : i ⟶ j) {E : SSet.{u}} (e : D.obj i ≅ E)
    (t : E ⟶ D.obj j) (ht : e.hom ≫ t = D.map h) :
    ((diagramSelectionEdge (diagramUniversalFamily D) h).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)).edge =
      (diagramSelectionTransportEdge (diagramSelectionAt D v) h e t ht).edge :=
  (diagramUniversalFamily_edge_evaluation D v h).trans
    (diagramSelectionTransportEdge_edge (diagramSelectionAt D v) h e t ht).symm

/-- 同じ全パラメーターの自然族の二脚を保つ、三角形の全選択空間。 -/
def diagramFamilyCospanPastingChoices {I : Type u} [SmallCategory I]
    {D : I ⥤ SSet.{u}} {P : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj P ⟶ D)
    {i j k : I} (h : i ⟶ k) (g : j ⟶ k) : SSet.{u} :=
  kanCospanPastingChoices
    (diagramSelectionEdge (diagramFamilyTranspose s) h)
    (diagramSelectionEdge (diagramFamilyTranspose s) g)

/-- 全パラメーターの二脚の貼り合わせも可縮 Kan。 -/
lemma diagramFamilyCospanPastingChoices_isContractibleKan {I : Type u} [SmallCategory I]
    {D : I ⥤ SSet.{u}} {P : SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj P ⟶ D)
    {i j k : I} (h : i ⟶ k) (g : j ⟶ k) [KanComplex (D.obj k)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (diagramFamilyCospanPastingChoices s h g) := by
  let : KanComplex ((D ⋙ ihom P).obj k) := by
    change KanComplex ((ihom P).obj (D.obj k))
    infer_instance
  exact kanCospanPastingChoices_isContractibleKan _ _

/-- 全選択空間を同時に動かして二脚を貼るための選択空間。 -/
def diagramUniversalCospanPastingChoices {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) {i j k : I} (h : i ⟶ k) (g : j ⟶ k) : SSet.{u} :=
  kanCospanPastingChoices (diagramSelectionEdge (diagramUniversalFamily D) h)
    (diagramSelectionEdge (diagramUniversalFamily D) g)

/-- 普遍族の貼り合わせは全ての高次選択を含む可縮 Kan 空間。 -/
lemma diagramUniversalCospanPastingChoices_isContractibleKan {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) {i j k : I} (h : i ⟶ k) (g : j ⟶ k)
    [KanComplex (D.obj k)] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (diagramUniversalCospanPastingChoices D h g) := by
  let : KanComplex ((D ⋙ ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D)).obj k) := by
    change KanComplex ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D)).obj (D.obj k))
    infer_instance
  exact kanCospanPastingChoices_isContractibleKan _ _

/-- 普遍族の貼り合わせを、全選択空間をパラメーターとする実際の二単体へ戻す。 -/
def diagramUniversalCospanPastingFamily {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) {i j k : I} (h : i ⟶ k) (g : j ⟶ k)
    (v : (diagramUniversalCospanPastingChoices D h g) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D ⊗ (Δ[2] : SSet.{u}) ⟶ D.obj k :=
  uncurry (kanCospanPastingAt (diagramSelectionEdge (diagramUniversalFamily D) h)
    (diagramSelectionEdge (diagramUniversalFamily D) g) v)

/-- 全パラメーターの三角形の 02 面は普遍族の第一脚そのもの。 -/
lemma diagramUniversalCospanPastingFamily_source {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) {i j k : I} (h : i ⟶ k) (g : j ⟶ k)
    (v : (diagramUniversalCospanPastingChoices D h g) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D ◁ stdSimplex.δ 1) ≫ diagramUniversalCospanPastingFamily D h g v =
      uncurry (SSet.yonedaEquiv.symm (diagramSelectionEdge (diagramUniversalFamily D) h).edge) := by
  dsimp only [diagramUniversalCospanPastingFamily]
  rw [← uncurry_natural_left, kanCospanPastingAt_source]

/-- 全パラメーターの三角形の 12 面は普遍族の第二脚そのもの。 -/
lemma diagramUniversalCospanPastingFamily_target {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) {i j k : I} (h : i ⟶ k) (g : j ⟶ k)
    (v : (diagramUniversalCospanPastingChoices D h g) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D ◁ stdSimplex.δ 0) ≫ diagramUniversalCospanPastingFamily D h g v =
      uncurry (SSet.yonedaEquiv.symm (diagramSelectionEdge (diagramUniversalFamily D) g).edge) := by
  dsimp only [diagramUniversalCospanPastingFamily]
  rw [← uncurry_natural_left, kanCospanPastingAt_target]

/-- 全選択を動かす源から標的への比較辺。 -/
def diagramUniversalCospanPastedEdge {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) {i j k : I} (h : i ⟶ k) (g : j ⟶ k)
    (v : (diagramUniversalCospanPastingChoices D h g) _⦋0⦌) :=
  kanCospanPastedEdge (diagramSelectionEdge (diagramUniversalFamily D) h)
    (diagramSelectionEdge (diagramUniversalFamily D) g) v

/-- 同じ全選択上の比較辺と元の二脚を両面に持つ実合成三角形。 -/
def diagramUniversalCospanPastedTriangle {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) {i j k : I} (h : i ⟶ k) (g : j ⟶ k)
    (v : (diagramUniversalCospanPastingChoices D h g) _⦋0⦌) :=
  kanCospanPastedTriangle (diagramSelectionEdge (diagramUniversalFamily D) h)
    (diagramSelectionEdge (diagramUniversalFamily D) g) v

/-- 普遍的な貼り合わせを評価すると、同じ選択の元の二脚を持つ実三角形になる。 -/
lemma diagramUniversalCospanPastedTriangle_evaluation {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) {i j k : I} (h : i ⟶ k) (g : j ⟶ k)
    (w : (diagramUniversalCospanPastingChoices D h g) _⦋0⦌)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D) _⦋0⦌) :
    ∃ e : (D.obj k).Edge
      ((D.map h).app (Opposite.op ⦋0⦌) (diagramSelectionVertex (diagramSelectionAt D v) i))
      ((D.map g).app (Opposite.op ⦋0⦌) (diagramSelectionVertex (diagramSelectionAt D v) j)),
      Nonempty (SSet.Edge.CompStruct e (diagramSelectionEdge (diagramSelectionAt D v) g)
        (diagramSelectionEdge (diagramSelectionAt D v) h)) ∧
      e.edge = ((diagramUniversalCospanPastedEdge D h g w).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)).edge :=
  kanCospanPastedTriangle_map (diagramSelectionEdge (diagramUniversalFamily D) h)
    (diagramSelectionEdge (diagramUniversalFamily D) g) w (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)
    (diagramSelectionEdge (diagramSelectionAt D v) h)
    (diagramSelectionEdge (diagramSelectionAt D v) g)
    (diagramUniversalFamily_edge_evaluation D v h) (diagramUniversalFamily_edge_evaluation D v g)

/-- 普遍的な貼り合わせの選択は、既存の任意の単射部分を固定して補完できる。 -/
lemma diagramUniversalCospanPastingChoices_relative_lifting {I : Type u} [SmallCategory I]
    (D : I ⥤ SSet.{u}) {i j k : I} (h : i ⟶ k) (g : j ⟶ k)
    [KanComplex (D.obj k)] {S T : SSet.{u}} (m : S ⟶ T) [Mono m]
    (a : S ⟶ diagramUniversalCospanPastingChoices D h g) :
    ∃ b : T ⟶ diagramUniversalCospanPastingChoices D h g, m ≫ b = a := by
  let : KanComplex ((D ⋙ ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D)).obj k) := by
    change KanComplex ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim D)).obj (D.obj k))
    infer_instance
  exact kanCospanPastingChoices_relative_lifting _ _ m a

end SerrePositivity.KST.SConstruction
