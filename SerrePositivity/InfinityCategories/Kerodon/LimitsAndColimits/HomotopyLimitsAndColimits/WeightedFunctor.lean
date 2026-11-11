module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSections
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：重み付き切断空間の図式に関する関手性と随伴。
方針：成分への射影で自然性を検証し、パラメーター付き自然変換との同値を随伴にする。
規約：保存するのは通常の単体集合の極限。Kan 性や ∞ 極限性を同時には主張しない。
使われ方：Kerodon 7.5.1.1（Tag 03A0）、7.5.4.6（Tag 03BB） の標準比較の自然性と図式の極限。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I]

/-- 概要：図式の自然変換は重み付き切断空間の射を誘導する。
方針：普遍的なパラメーター付き自然変換を後合成して持ち上げる。
規約：重み W は固定する。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の図式に関する関手性。 -/
noncomputable def weightedSectionsMap (W : I ⥤ SSet.{u}) {H H' : I ⥤ SSet.{u}}
    (η : H ⟶ H') : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H)) ≫ η)

/-- 概要：切断空間の誘導射は各内部 Hom で η の後合成になる。
方針：持ち上げの成分を計算し curry と uncurry を相殺する。
規約：成分は単体集合の射の厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の比較射の自然性。 -/
lemma weightedSectionsMap_π (W : I ⥤ SSet.{u}) {H H' : I ⥤ SSet.{u}}
    (η : H ⟶ H') (i : I) :
    weightedSectionsMap W η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H' i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i ≫ (ihom (W.obj i)).map (η.app i) := by
  rw [weightedSectionsMap, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π]
  change curry (uncurry (𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i) ≫ η.app i) = _
  rw [curry_natural_right, curry_uncurry, Category.id_comp]

/-- 概要：恒等自然変換は切断空間の恒等射を誘導する。
方針：全ての成分で内部 Hom の恒等保存を使う。
規約：重みの仮定は不要。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の関手則。 -/
lemma weightedSectionsMap_id (W H : I ⥤ SSet.{u}) :
    weightedSectionsMap W (𝟙 H) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [weightedSectionsMap_π]
  simp

/-- 概要：自然変換の合成は切断空間の射の合成を誘導する。
方針：各内部 Hom の合成保存を使う。
規約：合成の順序は通常の圏の順序。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の関手則。 -/
lemma weightedSectionsMap_comp (W : I ⥤ SSet.{u}) {H H' H'' : I ⥤ SSet.{u}}
    (η : H ⟶ H') (ε : H' ⟶ H'') :
    weightedSectionsMap W (η ≫ ε) = weightedSectionsMap W η ≫ weightedSectionsMap W ε := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [weightedSectionsMap_π, Category.assoc, weightedSectionsMap_π,
    ← Category.assoc, weightedSectionsMap_π]
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]

/-- 概要：重み付き切断を図式の圏から単体集合への関手にまとめる。
方針：構成した誘導射と二つの関手則を使う。
規約：値は同じ宇宙 u の単体集合。
使われ方：Kerodon 7.5.1.1（Tag 03A0）、Bousfield–Kan 型の構成の関手性。 -/
noncomputable def weightedSectionsFunctor (W : I ⥤ SSet.{u}) :
    (I ⥤ SSet.{u}) ⥤ SSet.{u} where
  obj H := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H
  map η := weightedSectionsMap W η
  map_id H := weightedSectionsMap_id W H
  map_comp η ε := weightedSectionsMap_comp W η ε

/-- 概要：持ち上げは図式の後合成に自然。
方針：各成分で curry の後合成の公式を使う。
規約：パラメーター A は任意。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の strict な錐の比較の自然性。 -/
lemma weightedSectionsLift_postcomp {W H H' : I ⥤ SSet.{u}} {A : SSet.{u}}
    (s : W ⊗ (Functor.const I).obj A ⟶ H) (η : H ⟶ H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (s ≫ η) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift s ≫ weightedSectionsMap W η := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π, Category.assoc, weightedSectionsMap_π,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π]
  exact curry_natural_right _ _

/-- 概要：切断の uncurry はパラメーターの前合成に自然。
方針：各成分で閉構造の自然性を使う。
規約：左因子である重みは固定する。
使われ方：Kerodon 7.5.1.1（Tag 03A0） のパラメーター付き普遍性。 -/
lemma weightedSectionsUncurry_precomp {W H : I ⥤ SSet.{u}} {A A' : SSet.{u}}
    (f : A' ⟶ A) (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (f ≫ g) =
      (W ◁ (Functor.const I).map f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry g := by
  apply NatTrans.ext
  funext i
  change uncurry ((f ≫ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i) =
    (W.obj i ◁ f) ≫ uncurry (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i)
  rw [Category.assoc, uncurry_natural_left]

/-- 概要：重みと定値図式との直積を作る関手。
方針：定値図式関手と図式の圏の左テンソルを合成する。
規約：左因子は W、右因子が入力の単体集合。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の end の通常の随伴表示。 -/
def weightedParameterFunctor (W : I ⥤ SSet.{u}) : SSet.{u} ⥤ (I ⥤ SSet.{u}) :=
  Functor.const I ⋙ tensorLeft W

/-- 概要：重み付き切断関手は重みとの直積を作る関手の右随伴。
方針：curry と end による Hom の同値と、その両変数の自然性を使う。
規約：これは通常の圏の随伴であり ∞ 随伴を前提にしない。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の重み付き end の極限保存。 -/
noncomputable def weightedSectionsAdjunction (W : I ⥤ SSet.{u}) :
    weightedParameterFunctor W ⊣ weightedSectionsFunctor W :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A H ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H A).symm
      homEquiv_naturality_left_symm := fun f g ↦ weightedSectionsUncurry_precomp f g
      homEquiv_naturality_right := fun s η ↦ weightedSectionsLift_postcomp s η }

/-- 概要：重み付き切断関手は通常の全てのサイズの極限を保存する。
方針：構成した右随伴に極限保存の一般定理を適用する。
規約：Kan 図式の ∞ 極限性をこの補題だけで結論しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の極限模型の計算と比較。 -/
noncomputable instance weightedSectionsFunctor_preservesLimits (W : I ⥤ SSet.{u}) :
    PreservesLimitsOfSize.{v, w} (weightedSectionsFunctor W) :=
  (weightedSectionsAdjunction W).rightAdjoint_preservesLimits

/-- 概要：錐の成分に整合する可換四角形は標準比較射にも整合する。
方針：全ての end の成分で curry の自然性と与えられた成分の等式を使う。
規約：錐の頂点と図式を同時に動かす。極限性や Kan 性は不要。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の sHom の始対象に関する比較の自然性。 -/
lemma weightedConeComparison_naturality (W : I ⥤ SSet.{u})
    {H H' : I ⥤ SSet.{u}} (c : Cone H) (d : Cone H') (f : c.pt ⟶ d.pt)
    (η : H ⟶ H') (h : ∀ i, f ≫ d.π.app i = c.π.app i ≫ η.app i) :
    f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W c ≫ weightedSectionsMap W η := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  conv_lhs => rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π, ← curry_natural_left]
  conv_rhs => rw [Category.assoc, weightedSectionsMap_π, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π, ← curry_natural_right]
  apply congrArg curry
  rw [whiskerLeft_snd_assoc, h, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
