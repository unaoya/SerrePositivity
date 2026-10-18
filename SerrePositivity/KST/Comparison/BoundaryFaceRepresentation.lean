module

public import SerrePositivity.KST.Comparison.BoundaryVertexFaces
public import SerrePositivity.KST.Comparison.SubcomplexPreimageIso
public import Mathlib.Data.Finset.Sort

/-!
# 境界の適切な面の標準単体表示

概要：頂点の昇順列挙を使い、非空な適切な面を低次元の標準単体と同定する。
方針：Mathlib の面の表現可能性と、部分対象の逆像の平坦化を合成する。
規約：Segal 1974 Proposition 1.6 の有限骨格の帰納。
使われ方：小さい行の比較を境界の各面へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory
open scoped Simplicial

/--
概要：適切な頂点集合の面は境界に含まれる。
方針：面が最大部分対象となる条件を頂点集合の全体性に帰着する。
規約：空の頂点集合も許す。
使われ方：境界への逆像を元の面と同定する。
-/
theorem vertexFace_le_boundary {n : ℕ} (S : Finset (Fin (n + 1)))
    (hS : S ≠ Finset.univ) : SSet.stdSimplex.face.{u} S ≤ SSet.boundary n := by
  apply (SSet.stdSimplex.le_boundary_iff _).mpr
  intro h
  apply hS
  apply le_antisymm (Finset.subset_univ S)
  apply (SSet.stdSimplex.face_le_face_iff _ _).mp
  rw [SSet.stdSimplex.face_univ, h]

/--
概要：面の昇順列挙に対応する単射な単体圏の射。
方針：有限順序集合の順序同型を頂点集合の包含と合成する。
規約：次元 m の頂点は m + 1 個。
使われ方：面の同型と標準単体への包含を結ぶ。
-/
def vertexFaceEmbedding {n m : ℕ} {S : Finset (Fin (n + 1))}
    (e : Fin (m + 1) ≃o S) : ⦋m⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk ((OrderHom.Subtype.val (· ∈ S)).comp
    e.toOrderEmbedding.toOrderHom)

/--
概要：面の昇順列挙による射は単射である。
方針：順序同型と部分型の包含の単射性を合成する。
規約：単体圏での mono として述べる。
使われ方：面の写像を骨格の面関係へ適用する。
-/
instance vertexFaceEmbedding_mono {n m : ℕ} {S : Finset (Fin (n + 1))}
    (e : Fin (m + 1) ≃o S) : Mono (vertexFaceEmbedding e) := by
  apply SimplexCategory.mono_iff_injective.mpr
  intro i j h
  apply e.injective
  exact Subtype.ext h

/--
概要：昇順列挙による標準単体と境界の面との同型。
方針：面の表現可能性の同型と、境界への逆像の同型の逆を合成する。
規約：頂点集合が適切であることを明示的に要求する。
使われ方：低次元の行のホモトピー引き戻しを各面へ運ぶ。
-/
def boundaryVertexFaceIso {n m : ℕ} {S : Finset (Fin (n + 1))}
    (hS : S ≠ Finset.univ) (e : Fin (m + 1) ≃o S) :
    Δ[m] ≅ (boundaryVertexFace.{u} n S : SSet.{u}) :=
  SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S m e) ≪≫
    (subcomplexPreimageIsoOfLE (SSet.stdSimplex.face S) (SSet.boundary n)
      (vertexFace_le_boundary S hS)).symm

/--
概要：面の表示の同型は、頂点の昇順列挙による標準単体の写像と両立する。
方針：各次数で単体の単調写像の合成を計算する。
規約：境界と標準単体への二つの包含を合成する。
使われ方：面での自然性の四角形を具体的な行の四角形へ同定する。
-/
theorem boundaryVertexFaceIso_hom_ι {n m : ℕ} {S : Finset (Fin (n + 1))}
    (hS : S ≠ Finset.univ) (e : Fin (m + 1) ≃o S) :
    (boundaryVertexFaceIso.{u} hS e).hom ≫ (boundaryVertexFace n S).ι ≫
      (SSet.boundary n).ι = SSet.stdSimplex.map (vertexFaceEmbedding e) := by
  rfl

/--
概要：非空な適切な面は、真に小さい次元の標準単体である。
方針：頂点数から次元を取り、有限順序集合の昇順列挙を使う。
規約：表示と周囲への包含の一致も結論に含める。
使われ方：Segal Proposition 1.6 の次元に関する強い帰納。
-/
theorem boundaryVertexFace_representation {n : ℕ} (S : Finset (Fin (n + 1)))
    (hS : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ (m : ℕ) (_ : m < n) (θ : ⦋m⦌ ⟶ ⦋n⦌) (_ : Mono θ)
      (e : Δ[m] ≅ (boundaryVertexFace.{u} n S : SSet.{u})),
      e.hom ≫ (boundaryVertexFace n S).ι ≫ (SSet.boundary n).ι =
        SSet.stdSimplex.map θ := by
  have hpos := Finset.card_pos.mpr hS
  have hlt : S.card < n + 1 := by
    have h := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ S, hproper⟩)
    simpa using h
  let m := S.card - 1
  have hcard : S.card = m + 1 := by dsimp [m]; omega
  let e := Finset.orderIsoOfFin S hcard
  refine ⟨m, by dsimp [m]; omega, vertexFaceEmbedding e, inferInstance,
    boundaryVertexFaceIso hproper e, boundaryVertexFaceIso_hom_ι hproper e⟩

end SerrePositivity.KST.Comparison
