module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
概要：単体的圏の strict な錐から、表現可能な図式の重み付き end への比較を構成する。
方針：単体的 Hom 関手で錐を写し、Bousfield–Kan 型の標準比較射を適用する。
規約：豊穣極限の同型は Hom 図式の極限性から得る。台の通常の極限性で代用しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の q_x = κ_x θ_x の構成。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：strict な図式 F に sHom(x,−) を適用した単体集合の図式。
方針：Mathlib の豊穣 Hom の共変関手との合成を使う。
規約：対象の宇宙 v と Hom の宇宙 u を区別する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の表現可能な図式 H_x。 -/
noncomputable def simplicialHomDiagram (F : I ⥤ C) (x : C) : I ⥤ SSet.{u} :=
  F ⋙ (SimplicialCategory.sHomFunctor C).obj (Opposite.op x)

/-- 概要：strict な錐に sHom(x,−) を適用した錐。
方針：豊穣 Hom 関手の錐への作用を使う。
規約：元の錐の極限性は仮定しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の各対象 x での homotopy 極限錐の判定。 -/
noncomputable def simplicialHomCone {F : I ⥤ C} (c : Cone F) (x : C) :
    Cone (simplicialHomDiagram F x) :=
  ((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).mapCone c

/-- 概要：局所 Kan な単体的圏の表現可能な図式は各点で Kan 複体。
方針：各成分の単体的 Hom に局所 Kan 性を適用する。
規約：図式の strict 極限の Kan 性はこの補題に含めない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の空間値図式という前提。 -/
instance simplicialHomDiagram_obj_kanComplex
    [∀ x y : C, KanComplex (SimplicialCategory.sHom x y)]
    (F : I ⥤ C) (x : C) (i : I) : KanComplex ((simplicialHomDiagram F x).obj i) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)))

/-- 概要：sHom(x,L) から表現可能な図式の Bousfield–Kan 型の end への比較射。
方針：sHom による錐に、構成済みの標準比較射を適用する。
規約：豊穣極限性や同値性を前提とせず、元の strict な錐から射を構成する。
使われ方：HTT 4.2.4.1 の双対の q_x。coherent な錐との比較は後続の証明対象。 -/
noncomputable def representableHomotopyLimitComparison {F : I ⥤ C} (c : Cone F) (x : C) :
    SimplicialCategory.sHom x c.pt ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (simplicialHomDiagram F x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (simplicialHomCone c x)

/-- 概要：豊穣極限錐の Hom の普遍性から標準の strict 極限との同型を得る。
方針：二つの極限錐の頂点の一意同型を使う。
規約：前提は sHom(x,−) による錐の極限性であり、元の通常の錐の極限性だけではない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の θ_x : sHom(x,L) ≅ lim sHom(x,F−)。 -/
noncomputable def enrichedLimitHomIso {F : I ⥤ C} (c : Cone F) (x : C)
    (h : IsLimit (simplicialHomCone c x)) :
    SimplicialCategory.sHom x c.pt ≅ limit (simplicialHomDiagram F x) :=
  h.conePointUniqueUpToIso (limit.isLimit _)

/-- 概要：豊穣極限の同型は元の錐の Hom 成分と整合する。
方針：極限錐間の一意同型の成分公式を使う。
規約：sHom の射のレベルでの厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の θ_x の向きの固定。 -/
lemma enrichedLimitHomIso_π {F : I ⥤ C} (c : Cone F) (x : C)
    (h : IsLimit (simplicialHomCone c x)) (i : I) :
    (enrichedLimitHomIso c x h).hom ≫ limit.π (simplicialHomDiagram F x) i =
      (simplicialHomCone c x).π.app i :=
  h.conePointUniqueUpToIso_hom_comp (limit.isLimit _) i

/-- 概要：錐から直接構成した比較射は、豊穣極限の同型と標準比較射の合成に一致する。
方針：重み付き end の各成分で curry の自然性と θ_x の成分公式を使う。
規約：θ_x や κ_x の選択に置き換えず、既存の標準比較射の等式を証明する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の q_x = κ_x θ_x。 -/
lemma representableHomotopyLimitComparison_factorization {F : I ⥤ C} (c : Cone F) (x : C)
    (h : IsLimit (simplicialHomCone c x)) :
    representableHomotopyLimitComparison c x =
      (enrichedLimitHomIso c x h).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison (simplicialHomDiagram F x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (simplicialHomCone c x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ _ _ i =
    ((enrichedLimitHomIso c x h).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (limit.cone _)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ _ _ i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π]
  conv_rhs => rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π, ← curry_natural_left]
  congr 1
  change snd ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i) (SimplicialCategory.sHom x c.pt) ≫
      (simplicialHomCone c x).π.app i =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i ◁ (enrichedLimitHomIso c x h).hom) ≫
      snd ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i) (limit (simplicialHomDiagram F x)) ≫
        limit.π (simplicialHomDiagram F x) i
  conv_rhs => rw [← Category.assoc, whiskerLeft_snd, Category.assoc, enrichedLimitHomIso_π]

/-- 概要：sHom の始対象の射は表現可能な単体集合の図式の自然変換を誘導する。
方針：豊穣 Hom の反変関手の射を F で制限する。
規約：x → y に対して sHom(y,F−) → sHom(x,F−) の向き。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の全対象 x に関する自然性。 -/
noncomputable def simplicialHomDiagramPre (F : I ⥤ C) {x y : C} (f : x ⟶ y) :
    simplicialHomDiagram F y ⟶ simplicialHomDiagram F x :=
  Functor.whiskerLeft F ((SimplicialCategory.sHomFunctor C).map f.op)

/-- 概要：構成した表現可能な homotopy 極限の比較射は始対象に反変自然。
方針：豊穣 Hom の二変数の自然性を、錐の比較の可換四角形の公式に渡す。
規約：同値の選択による自然性ではなく実際の標準射の厳密な自然性。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の表現可能な判定。 -/
lemma representableHomotopyLimitComparison_naturality {F : I ⥤ C} (c : Cone F)
    {x y : C} (f : x ⟶ y) :
    ((SimplicialCategory.sHomFunctor C).map f.op).app c.pt ≫
        representableHomotopyLimitComparison c x =
      representableHomotopyLimitComparison c y ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor I).map (simplicialHomDiagramPre F f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (simplicialHomCone c y) (simplicialHomCone c x) _ _
    (fun i ↦ (((SimplicialCategory.sHomFunctor C).map f.op).naturality (c.π.app i)).symm)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
