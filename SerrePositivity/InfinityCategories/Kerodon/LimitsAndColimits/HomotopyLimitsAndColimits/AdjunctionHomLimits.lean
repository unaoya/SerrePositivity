module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.GeneralOriginalCriterion
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
概要：通常の随伴と整合する自然な単体的 Hom 同型から native な極限の保存を導く。
方針：Hom 同型が作る元の Bousfield–Kan 比較の可換正方形で同値性を移す。
規約：Hom 同型を明示し、通常の Quillen 条件だけからの存在は仮定しない。
使われ方：HTT 4.2.4.1・5.2.4.6、Kerodon 7.5.4.6（Tag 03BB）、右導来関手の極限保存への接続。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section
variable {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] {L : C ⥤ D} {R : D ⥤ C}

/-- 概要：指定した通常の随伴と零単体で一致する、終域に自然な単体的 Hom 同型。
方針：各 x の表現可能な関手の自然同型と零単体の一致を部分型に束縛する。
規約：終域 y の全単体で自然、始域 x での追加の豊穣自然性は要求しない。
使われ方：HTT 5.2.4.6、右随伴の strict な homotopy 極限保存に必要な Hom データ。 -/
def SimplicialAdjunctionHomIso (adj : L ⊣ R) :=
  {e : ∀ x : C, (SimplicialCategory.sHomFunctor D).obj (Opposite.op (L.obj x)) ≅
      R ⋙ (SimplicialCategory.sHomFunctor C).obj (Opposite.op x) //
    ∀ (x : C) (y : D) (f : L.obj x ⟶ y),
      ((e x).hom.app y).app (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' _ _ f) =
        SimplicialCategory.homEquiv' _ _ (adj.homEquiv x y f)}

/-- 概要：単体的 Hom 同型の零単体への作用は指定した通常の随伴の Hom 全単射。
方針：部分型の整合性の条件を取り出す。
規約：通常の随伴を別の選択へ替えない。
使われ方：E2b の Hom 比較と既存の通常の Quillen 随伴の照合。 -/
lemma simplicialAdjunctionHomIso_zero {adj : L ⊣ R} (e : SimplicialAdjunctionHomIso adj)
    (x : C) (y : D) (f : L.obj x ⟶ y) :
    ((e.val x).hom.app y).app (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' _ _ f) =
      SimplicialCategory.homEquiv' _ _ (adj.homEquiv x y f) := e.property x y f

variable {I : Type u} [SmallCategory I]

/-- 概要：随伴の単体的 Hom 同型は任意の図式の表現可能な係数図式の自然同型を与える。
方針：各成分で Hom 同型を取り、元の自然同型の自然性を構造射へ制限する。
規約：元の F の射を変えず、右随伴の通常の合成 F ⋙ R を使う。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、Bousfield–Kan end の係数の同型。 -/
def simplicialAdjunctionHomDiagramIso {adj : L ⊣ R} (e : SimplicialAdjunctionHomIso adj)
    (F : I ⥤ D) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (L.obj x) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (F ⋙ R) x :=
  NatIso.ofComponents (fun i ↦ (e.val x).app (F.obj i)) (by
    intro i j f
    exact (e.val x).hom.naturality (F.map f))

/-- 概要：随伴の Hom 同型は元の比較 q の頂点と end の厳密な可換正方形を作る。
方針：重み付き錐の比較の自然性に Hom 同型の頂点と図式の自然変換を渡す。
規約：局所 Kan 性・錐の極限性はこの可換式に不要。
使われ方：HTT 4.2.4.1・5.2.4.6、右随伴による homotopy 極限の比較射の保存。 -/
lemma representableComparison_adjunction_square {adj : L ⊣ R}
    (e : SimplicialAdjunctionHomIso adj) {F : I ⥤ D} (c : Cone F) (x : C) :
    ((e.val x).app c.pt).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison (R.mapCone c) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c (L.obj x) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
          (simplicialAdjunctionHomDiagramIso e F x).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone c (L.obj x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (R.mapCone c) x)
    ((e.val x).app c.pt).hom (simplicialAdjunctionHomDiagramIso e F x).hom
  intro i
  exact ((e.val x).hom.naturality (c.π.app i)).symm

/-- 概要：随伴の単体的 Hom 同型の下で、左像で測る元の q と右像の錐の q の同値性が一致する。
方針：Hom 同型の頂点と end の同型の同値性を可換正方形で消去する。
規約：両圏の局所 Kan 性のみを要求し、Hom の厳密極限性は仮定しない。
使われ方：HTT 5.2.4.6、右随伴による任意の strict な homotopy 極限の保存。 -/
lemma representableComparison_adjunction_homotopyEquivalence_iff
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    {adj : L ⊣ R} (e : SimplicialAdjunctionHomIso adj) {F : I ⥤ D} (c : Cone F) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison c (L.obj x)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison (R.mapCone c) x) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (L.obj x))
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (F ⋙ R) x)
  have : KanComplex (((SimplicialCategory.sHomFunctor D).obj
      (Opposite.op (L.obj x))).obj c.pt) :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom (L.obj x) c.pt))
  have : KanComplex ((R ⋙ (SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).obj c.pt) :=
    inferInstanceAs (KanComplex (SimplicialCategory.sHom x (R.obj c.pt)))
  let η := simplicialAdjunctionHomDiagramIso e F x
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η.hom) := by
    change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)).map η.hom)
    infer_instance
  have hE := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η.hom)
  have hV := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso ((e.val x).app c.pt).hom
  constructor
  · intro h
    have he := h.comp hE
    rw [← representableComparison_adjunction_square e c x] at he
    exact hV.cancel_left he
  · intro h
    have he := hV.comp h
    rw [representableComparison_adjunction_square e c x] at he
    exact hE.cancel_right he

/-- 概要：自然な単体的 Hom 随伴同型を持つ右随伴は strict な表示の native な極限を保つ。
方針：元の錐の全 q の同値性を各 Lx で取り、Hom 同型で右像の錐へ移す。
規約：任意の小圏の図式で、fibration 条件や厳密極限性を追加しない。
使われ方：HTT 4.2.4.1・5.2.4.6、E2b の右導来忘却関手の極限保存への共有界面。 -/
lemma strictCoherentCone_map_isLimit_of_adjunctionHomIso
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    {adj : L ⊣ R} (e : SimplicialAdjunctionHomIso adj) {F : I ⥤ D} (c : Cone F)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (R.mapCone c)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_general_representableComparison _).mpr
  intro x
  apply (representableComparison_adjunction_homotopyEquivalence_iff e c x).mp
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_general_representableComparison c).mp hc (L.obj x)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
