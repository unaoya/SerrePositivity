module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SequentialFactorLift
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryRightColimit
public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitWeakEquivalence

/-!
# 逐次図式の局所化可逆な比較は実際の余極限上でも局所化可逆となる

## 概要
逐次図式の局所化可逆な比較は実際の余極限上でも局所化可逆となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。
[棚卸し m0436][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0436
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Sequential colimit comparison in the original anodyne localization

The source successor maps are mono and all original components are
localized equivalences. Relative lifting handles the left colimit factor;
finite boundary presentability handles the right factor. No value model
structure or preservation of colimits by the localization is assumed.
-/

@[expose] public section
universe v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanSequentialColimitComparison
open SequentialBoundaryFactorization SequentialFactorLiftingClasses KanTestLiftingClass
variable {F G : ℕ ⥤ SSet.{v}} (α : F ⟶ G)
  (hF : ∀ n, Mono (stepMap F n))
  (hα : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (α.app n)))

include hF hα in
lemma left_colimit_llp : rightTests.llp (colim.map (leftMap α)) := by
  intro X Y p hp
  apply (Adjunction.hasLiftingProperty_iff colimConstAdj (leftMap α) p).mpr
  apply SequentialFactorLift.hasLiftingProperty α p
  · exact initial_llp α (hα 0) _ hp
  · intro n
    have : Mono (stepMap F n) := hF n
    exact relative_llp α n hα _ hp

lemma right_colimit_rlp : SSet.modelCategoryQuillen.I.rlp (colim.map (rightMap α)) :=
  BoundaryRightColimit.sequential_rlp
    (DiagramModel.arrowColimitCoconeIsColimit (rightMap α)) (right_boundary_rlp α)

include hF hα in
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (colim.map α)) := by
  have hl : IsIso (AnodyneHomotopy.anodyneQ.map (colim.map (leftMap α))) :=
    localized_isIso_of_llp _ (left_colimit_llp α hF hα)
  have hr : IsIso (AnodyneHomotopy.anodyneQ.map (colim.map (rightMap α))) := by
    have h := right_colimit_rlp α
    rw [← SSet.rlp_monomorphisms] at h
    exact MonoRightLiftingContraction.localized_isIso _ h
  have he : colim.map (leftMap α) ≫ colim.map (rightMap α) = colim.map α :=
    (colim.map_comp _ _).symm.trans (congrArg colim.map (factorization_eq α))
  have h := congrArg AnodyneHomotopy.anodyneQ.map he
  rw [CategoryTheory.Functor.map_comp] at h
  exact h ▸ inferInstanceAs (IsIso
    (AnodyneHomotopy.anodyneQ.map (colim.map (leftMap α)) ≫
      AnodyneHomotopy.anodyneQ.map (colim.map (rightMap α))))

include hF hα in
/-- 逐次図式の局所化可逆な比較は実際の余極限上でも局所化可逆となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。
-/
lemma actual_localized_isIso (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (m : c.pt ⟶ d.pt) (hm : ∀ n, c.ι.app n ≫ m = α.app n ≫ d.ι.app n) :
    IsIso (AnodyneHomotopy.anodyneQ.map m) := by
  let e := hc.coconePointUniqueUpToIso (colimit.isColimit F)
  let e' := hd.coconePointUniqueUpToIso (colimit.isColimit G)
  have he : e.hom ≫ colim.map α = m ≫ e'.hom := by
    apply hc.hom_ext
    intro n
    rw [← Category.assoc, hc.comp_coconePointUniqueUpToIso_hom]
    change colimit.ι F n ≫ colim.map α = _
    rw [colimit.ι_map, ← Category.assoc, hm n, Category.assoc]
    dsimp only [e']
    rw [hd.comp_coconePointUniqueUpToIso_hom]
    rfl
  have : IsIso (AnodyneHomotopy.anodyneQ.map (colim.map α)) := localized_isIso α hF hα
  have h := congrArg AnodyneHomotopy.anodyneQ.map he
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  have : IsIso (AnodyneHomotopy.anodyneQ.map m ≫ AnodyneHomotopy.anodyneQ.map e'.hom) :=
    h ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp this

include hF hα in
lemma image_isIso {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map (colim.map α)) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _ (localized_isIso α hF hα)

end SerrePositivity.SimplicialModel.KanSequentialColimitComparison
