module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.SubcomplexRestriction

/-!
概要：有限個の面の和と、その上に制限した解像の射影。
方針：部分複体の有限上限を取り、面との交わりを頂点集合の交わりへ分配する。
規約：面族は頂点集合の有限集合で表し、重複する面を区別しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界上の比較の有限帰納法。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：指定した有限個の面の解像の和。
方針：旗の台で定めた面の有限上限を取る。
規約：空の面族の和は空の部分複体。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、解像の境界の有限の貼り合わせ。 -/
def coherentResolutionFaceUnion {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex := S.sup _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace

/-- 概要：同じ頂点集合の面族が定める標準単体の部分複体。
方針：標準単体の面の有限上限を取る。
規約：解像側と同じ面族を使う。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、貼り合わせる射影の標的。 -/
def stdSimplexFaceUnion {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    (Δ[n] : SSet.{u}).Subcomplex := S.sup stdSimplex.face

/-- 概要：面の和への所属は、いずれかの面が旗の台を含むこと。
方針：有限上限を部分複体の次数ごとの集合の和に展開する。
規約：旗の全次数に適用する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、和の上で射影の所属を確認する。 -/
lemma mem_coherentResolutionFaceUnion_iff {n : ℕ} (S : Finset (Finset (Fin (n + 1))))
    {d : SimplexCategoryᵒᵖ} (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).obj d) :
    F ∈ (coherentResolutionFaceUnion S).obj d ↔ ∃ T ∈ S, F.down.support ⊆ T := by
  simp only [coherentResolutionFaceUnion, Finset.sup_eq_iSup, Subfunctor.iSup_obj,
    Set.mem_iUnion, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, hT, hF⟩
    exact ⟨T, hT, hF⟩
  · rintro ⟨T, hT, hF⟩
    exact ⟨T, hT, hF⟩

/-- 概要：空の面族の解像の和は空。
方針：有限上限の空族の計算を使う。
規約：有限帰納法の基底。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、貼り合わせの基底。 -/
lemma coherentResolutionFaceUnion_empty (n : ℕ) :
    coherentResolutionFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) = ⊥ := rfl

/-- 概要：空の面族の標準単体の和は空。
方針：有限上限の空族の計算を使う。
規約：解像側と対応する基底。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標的側の貼り合わせの基底。 -/
lemma stdSimplexFaceUnion_empty (n : ℕ) :
    stdSimplexFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) = ⊥ := rfl

/-- 概要：面を一つ加えた解像の和は元の和との上限。
方針：有限上限の insert の計算を使う。
規約：面の重複の有無を問わない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、有限帰納法の帰納段階。 -/
lemma coherentResolutionFaceUnion_insert {n : ℕ} (T : Finset (Fin (n + 1)))
    (S : Finset (Finset (Fin (n + 1)))) :
    coherentResolutionFaceUnion.{u} (insert T S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T ⊔ coherentResolutionFaceUnion S := by
  classical
  exact Finset.sup_insert

/-- 概要：面を一つ加えた標準単体の和は元の和との上限。
方針：有限上限の insert の計算を使う。
規約：解像側と同じ順序で和を取る。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標的側の帰納段階。 -/
lemma stdSimplexFaceUnion_insert {n : ℕ} (T : Finset (Fin (n + 1)))
    (S : Finset (Finset (Fin (n + 1)))) :
    stdSimplexFaceUnion.{u} (insert T S) = stdSimplex.face T ⊔ stdSimplexFaceUnion S := by
  classical
  exact Finset.sup_insert

/-- 概要：有限個の部分複体の和と交わりは分配する。
方針：各次数の集合の所属に展開し、和の所属の証人を移す。
規約：部分複体の分配束のインスタンスを要求しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、面の和と交わりの計算。 -/
lemma subcomplex_finsetSup_inf {X : SSet.{u}} {ι : Type*} (S : Finset ι)
    (F : ι → X.Subcomplex) (A : X.Subcomplex) :
    S.sup F ⊓ A = S.sup (fun i ↦ F i ⊓ A) := by
  apply Subfunctor.ext
  funext d
  change (S.sup F).obj d ∩ A.obj d = (S.sup (fun i ↦ F i ⊓ A)).obj d
  simp only [Finset.sup_eq_iSup, Subfunctor.iSup_obj]
  apply Set.ext
  intro x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi, hx⟩, ha⟩
    exact ⟨i, hi, hx, ha⟩
  · rintro ⟨i, hi, hx, ha⟩
    exact ⟨⟨i, hi, hx⟩, ha⟩

/-- 概要：解像の面の和と一つの面の交わりは、交わった面の有限和。
方針：有限上限に下限を分配し、面の交わりの計算を使う。
規約：交わりによって同じ面が生じても有限集合の image が重複を除く。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、交わりを小さい面族へ帰着する。 -/
lemma coherentResolutionFaceUnion_inf_face {n : ℕ} (S : Finset (Finset (Fin (n + 1))))
    (T : Finset (Fin (n + 1))) :
    coherentResolutionFaceUnion.{u} S ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T =
      coherentResolutionFaceUnion (S.image (fun U ↦ U ∩ T)) := by
  classical
  simp only [coherentResolutionFaceUnion, subcomplex_finsetSup_inf, Finset.sup_image]
  congr 1
  funext U
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace_inter U T).symm

/-- 概要：標準単体の面の和と面の交わりも、交わった面の有限和。
方針：有限上限の分配と標準単体の面の交わりを使う。
規約：解像側と同じ面族の image を使う。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標的の交わりの帰納的表示。 -/
lemma stdSimplexFaceUnion_inf_face {n : ℕ} (S : Finset (Finset (Fin (n + 1))))
    (T : Finset (Fin (n + 1))) :
    stdSimplexFaceUnion.{u} S ⊓ stdSimplex.face T =
      stdSimplexFaceUnion (S.image (fun U ↦ U ∩ T)) := by
  classical
  simp only [stdSimplexFaceUnion, subcomplex_finsetSup_inf, Finset.sup_image,
    stdSimplex.face_inter_face]
  congr 1

/-- 概要：解像の面の和は射影で同じ標準単体の面の和へ写る。
方針：所属する一つの面を選び、その面の射影の所属条件を使う。
規約：面族の空性や面の非空性を仮定しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、和の上の射影の制限条件。 -/
lemma coherentResolutionFaceUnion_mapsTo {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    coherentResolutionFaceUnion.{u} S ≤ (stdSimplexFaceUnion S).preimage
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n) := by
  intro d F hF
  obtain ⟨T, hT, hFT⟩ := (mem_coherentResolutionFaceUnion_iff S F).mp hF
  have hface : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n).app d F ∈ (stdSimplex.face T).obj d := by
    change Finset.univ.image F.down.maxAt ⊆ T
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact hFT (F.down.sets_subset_support j (F.down.maxAt_mem j))
  have hle : stdSimplex.face.{u} T ≤ stdSimplexFaceUnion S := Finset.le_sup hT
  exact hle d hface

/-- 概要：有限個の面の和上の解像の射影。
方針：大きい解像の射影を対応する二つの和へ制限する。
規約：制限条件は面族だけから定まる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の射影への有限帰納法。 -/
def coherentResolutionFaceUnionProjection {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    (coherentResolutionFaceUnion.{u} S).toSSet ⟶ (stdSimplexFaceUnion S).toSSet :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.subcomplexRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n) _ _ (coherentResolutionFaceUnion_mapsTo S)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
