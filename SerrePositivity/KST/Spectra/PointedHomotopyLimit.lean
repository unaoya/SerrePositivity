module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionsKan
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：点つき Kan 図式の段ごとの Bousfield–Kan end の点つき構成。
方針：基点の錐を重み付き end へ送り、既存の実際のホーン充填による Kan 性を使う。
規約：借用するのは end と Kan 性。Sp の ∞ 極限性を主張しない。
使われ方：BF 1978 §2、HA §1.4.2、Kerodon 7.5.4.6（Tag 03BB）。L9e の hG と Tot のレベルごとの構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.PointedHomotopyLimit

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false



variable {I : Type u} [SmallCategory I]

/-- 概要：点つき図式の基点は忘却した図式の錐をなす。
方針：各成分は各対象の基点を選ぶ射。
規約：錐の頂点は単体集合の終対象。
使われ方：BF 1978 §2、Kerodon 7.5.4.1（Tag 03B6）。end の基点の構成。 -/
def basepointCone (D : I ⥤ PointedSimplicialSet.{u}) :
    Cone (D ⋙ PointedSimplicialSet.forget) where
  pt := 𝟙_ SSet.{u}
  π := {
    app i := (D.obj i).hom
    naturality i j f := by
      change 𝟙 (𝟙_ SSet.{u}) ≫ (D.obj j).hom = (D.obj i).hom ≫ (D.map f).right
      rw [Category.id_comp]
      exact (Under.w (D.map f)).symm }

/-- 概要：点つき図式の Bousfield–Kan end。
方針：基点の錐の比較射を基点として指定する。
規約：値は点つき単体集合。Kan 性は別に各対象の Kan 性から示す。
使われ方：BF 1978 §2、HA §1.4.2、Kerodon 7.5.4.6（Tag 03BB）。hG と Tot の各段。 -/
def obj (D : I ⥤ PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  Under.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (basepointCone D))

/-- 概要：点つき図式の自然変換が end に誘導する点つき射。
方針：重み付き end の後合成と基点の錐の自然性を使う。
規約：通常の点つき射として厳密。
使われ方：BF 1978 §2、Kerodon 7.5.4.6（Tag 03BB）。作用と余単体対象の射への作用。 -/
def map {D E : I ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) : obj D ⟶ obj E :=
  Under.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      (Functor.whiskerRight τ PointedSimplicialSet.forget))
    (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (basepointCone D) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
          (Functor.whiskerRight τ PointedSimplicialSet.forget) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (basepointCone E)
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
        (basepointCone D) (basepointCone E) (𝟙 (𝟙_ SSet.{u}))
        (Functor.whiskerRight τ PointedSimplicialSet.forget)
        (fun i ↦ by
          change 𝟙 (𝟙_ SSet.{u}) ≫ (E.obj i).hom = (D.obj i).hom ≫ (τ.app i).right
          rw [Category.id_comp]
          exact (Under.w (τ.app i)).symm)
      change 𝟙 (𝟙_ SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (basepointCone E) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (basepointCone D) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
            (Functor.whiskerRight τ PointedSimplicialSet.forget) at h
      rw [Category.id_comp] at h
      exact h.symm)

/-- 概要：Kan 図式の点つき end の基礎単体集合は Kan。
方針：N レーンの切断空間でのホーン充填による Kan 性を借りる。
規約：一般の厳密極限の Kan 性を仮定しない。
使われ方：BF 1978 §2、Kerodon 7.5.4.6（Tag 03BB）。hG と Tot のレベルごとの Kan 性。 -/
instance kanComplex (D : I ⥤ PointedSimplicialSet.{u}) [∀ i, KanComplex (D.obj i).right] :
    KanComplex (obj D).right := by
  let : ∀ i, KanComplex ((D ⋙ PointedSimplicialSet.forget).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (D.obj i).right)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (D ⋙ PointedSimplicialSet.forget)

/-- 概要：点つき end は恒等自然変換を恒等射へ送る。
方針：基礎の重み付き end の恒等法則を使う。
規約：点つき射の厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB）。レベルごとの構成の関手法則。 -/
theorem map_id (D : I ⥤ PointedSimplicialSet.{u}) : map (𝟙 D) = 𝟙 (obj D) := by
  apply Under.UnderMorphism.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_id (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (D ⋙ PointedSimplicialSet.forget)

/-- 概要：点つき end は自然変換の合成を保つ。
方針：基礎の重み付き end の合成法則を使う。
規約：点つき射の厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB）。hG と Tot の射への作用。 -/
theorem map_comp {D E F : I ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) (υ : E ⟶ F) :
    map (τ ≫ υ) = map τ ≫ map υ := by
  apply Under.UnderMorphism.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (Functor.whiskerRight τ PointedSimplicialSet.forget)
    (Functor.whiskerRight υ PointedSimplicialSet.forget)

/-- 概要：点つき図式の Bousfield–Kan end を通常の関手に束ねる。
方針：実際の射と恒等・合成法則を用いる。
規約：Sp の ∞ 極限関手という主張は含まない。
使われ方：BF 1978 §2、HA §1.4.2。hG・Tot を段ごとに適用する入力。 -/
def functor (I : Type u) [SmallCategory I] :
    (I ⥤ PointedSimplicialSet.{u}) ⥤ PointedSimplicialSet.{u} where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

end

end SerrePositivity.KST.Spectra.PointedHomotopyLimit
