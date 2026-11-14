module


public meta import SerrePositivity.Util.Citation
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# ホモトピー圏の二つの構成の比較

概要：辺のホモトピー類による圏と、辺の道を二単体の関係で割った圏を比較する。
方針：道から辺の類への関手を普遍性で作り、逆向きは商から降ろす。
規約：合成は Mathlib の `≫` の順。追加のモデル構造は用いない。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） のホモトピー圏を既存 API に接続する。

対応節は Kerodon 1.4（Tag 0039）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet SSet.Truncated SimplicialObject.Truncated

namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

variable (A : SSet.Truncated.{u} 2) [Quasicategory₂ A]

/-- 概要：辺の道の商から辺のホモトピー類の圏への関手。
方針：二単体の合成関係を `homotopyCategory₂_fac` で保存し、普遍性で延長する。
規約：対象の頂点と辺の向きを保つ。仮定は二切断の内部ホーン充填。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の比較同値の逆関手。 -/
noncomputable def pathToEdgeHomotopyCategory : A.HomotopyCategory ⥤ HomotopyCategory₂ A :=
  HomotopyCategory.lift HomotopyCategory₂.mk (fun e ↦ HomotopyCategory₂.homMk e)
    (fun _ ↦ rfl) (fun h ↦ h.homotopyCategory₂_fac)

omit [Quasicategory₂ A] in
/-- 概要：左ホモトピックな辺は道の商で等しい。
方針：退化辺との合成二単体を使う。規約：充填の仮定は不要。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の商への写像の降下。 -/
lemma homotopic_path_eq {x y : A _⦋0⦌₂} {f g : Edge x y}
    (h : HomotopicL f g) : HomotopyCategory.homMk f = HomotopyCategory.homMk g := by
  obtain ⟨h⟩ := h
  simpa using HomotopyCategory.homMk_comp_homMk h

/-- 概要：辺のホモトピー類から辺の道の商への関手。
方針：左ホモトピーを退化辺との合成関係として消し、商から写像を降ろす。
規約：合成保存は選んだ合成二単体から従い、その選択には依存しない。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の比較同値の順関手。 -/
noncomputable def edgeToPathHomotopyCategory : HomotopyCategory₂ A ⥤ A.HomotopyCategory where
  obj x := HomotopyCategory.mk x.pt
  map := Quotient.lift (fun e ↦ HomotopyCategory.homMk e)
    (fun _ _ h ↦ homotopic_path_eq A h)
  map_id x := HomotopyCategory.homMk_id x.pt
  map_comp := by
    rintro _ _ _ ⟨f⟩ ⟨g⟩
    exact (HomotopyCategory.homMk_comp_homMk (Edge.compStruct f g)).symm

/-- 概要：辺の類から道を経由して戻る関手は恒等。
方針：商の代表元上で検証する。規約：二切断 quasicategory を仮定。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の比較同値の単位。 -/
lemma edge_path_inverse :
    edgeToPathHomotopyCategory A ⋙ pathToEdgeHomotopyCategory A = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (F := edgeToPathHomotopyCategory A ⋙
    pathToEdgeHomotopyCategory A) (G := 𝟭 _) (fun _ ↦ rfl) ?_
  rintro _ _ ⟨f⟩
  change (pathToEdgeHomotopyCategory A).map (HomotopyCategory.homMk f) = _
  simp only [pathToEdgeHomotopyCategory, HomotopyCategory.lift_map_homMk,
    eqToHom_refl, Category.id_comp, Category.comp_id, Functor.id_map,
    HomotopyCategory₂.homMk]
  rfl

/-- 概要：道から辺の類を経由して戻る関手は恒等。
方針：道の生成元である辺上で検証する。規約：二切断 quasicategory を仮定。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の比較同値の余単位。 -/
lemma path_edge_inverse :
    pathToEdgeHomotopyCategory A ⋙ edgeToPathHomotopyCategory A = 𝟭 _ := by
  apply HomotopyCategory.functor_ext (F := pathToEdgeHomotopyCategory A ⋙
    edgeToPathHomotopyCategory A) (G := 𝟭 _) (fun _ ↦ rfl)
  intro x y e
  change (edgeToPathHomotopyCategory A).map
    ((pathToEdgeHomotopyCategory A).map (HomotopyCategory.homMk e)) = _
  simp [pathToEdgeHomotopyCategory, HomotopyCategory.lift_map_homMk,
    edgeToPathHomotopyCategory, HomotopyCategory₂.homMk]

/-- 概要：quasicategory の辺のホモトピー類による圏は Mathlib の `hoFunctor` と同値。
方針：二つの比較関手の合成が恒等であることを辺の生成元上で示す。
規約：仮定は Mathlib の `Quasicategory` のみ。標準三公理以外を使わない。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） のホモトピー圏を dg nerve 等に適用する橋。 -/
@[kerodon 004C]
noncomputable def homotopyCategoryBridge (X : SSet.{u}) [Quasicategory X] :
    HomotopyCategory₂ ((truncation 2).obj X) ≌ hoFunctor.obj X :=
  CategoryTheory.Equivalence.mk (edgeToPathHomotopyCategory _) (pathToEdgeHomotopyCategory _)
    (eqToIso (edge_path_inverse _).symm) (eqToIso (path_edge_inverse _))

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.3.9"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge
attribute [cite HTT "1.2.3.9"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory
