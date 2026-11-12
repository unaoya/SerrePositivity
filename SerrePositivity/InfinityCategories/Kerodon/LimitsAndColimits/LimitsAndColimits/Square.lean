module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

/-!
概要：cospan の錐と正方形の単体集合の同型。
方針：両方を対角に沿った二つの標準三角形の pushout として表示する。
規約：cospan は Λ[2,2]、正方形は Δ[1]⊗Δ[1]。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の引き戻し四角形。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：標準単体の積の非退化単体の Yoneda 射は単射。
方針：有限順序集合への頂点写像が単射であることを次数ごとの写像に用いる。
規約：任意の p、q、n を扱う。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の正方形の三角形の像。 -/
lemma mono_yoneda_prod_nonDegenerate {p q n : ℕ}
    (s : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n) : Mono (SSet.yonedaEquiv.symm s.val) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  rw [mono_iff_injective]
  intro a b hab
  apply stdSimplex.ext
  intro i
  apply (prodStdSimplex.nonDegenerate_iff_injective_objEquiv s.val).1 s.property
  have hv := congrArg (fun z ↦ prodStdSimplex.objEquiv z i) hab
  exact hv

/-- 概要：正方形の二つの非退化三角形。
方針：Mathlib の標準単体と辺の積の列挙を使う。
規約：i=0 は (0,0),(0,1),(1,1)、i=1 は (0,0),(1,0),(1,1)。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の二三角形への分解。 -/
noncomputable def squareTriangleSimplex (i : Fin 2) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}).nonDegenerate 2 :=
  prodStdSimplex₁.nonDegenerateEquiv i

/-- 概要：正方形の対角の非退化辺。
方針：Mathlib の codimOneSimplex の中間のものを使う。
規約：頂点は (0,0) と (1,1)。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の三角形の共通部分。 -/
def squareDiagonalSimplex : (Δ[1] ⊗ Δ[1] : SSet.{u}).nonDegenerate 1 :=
  prodStdSimplex₁.codimOneSimplex 1

/-- 概要：正方形への標準三角形の包含。
方針：非退化三角形の Yoneda 射を使う。
規約：番号は squareTriangleSimplex と一致する。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の正方形の貼り合わせ。 -/
noncomputable def squareTriangle (i : Fin 2) : (Δ[2] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  SSet.yonedaEquiv.symm (squareTriangleSimplex i).val

/-- 概要：正方形への対角の包含。
方針：対角の非退化辺の Yoneda 射を使う。
規約：向きは (0,0) から (1,1)。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の正方形の共通の辺。 -/
def squareDiagonal : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  SSet.yonedaEquiv.symm squareDiagonalSimplex.val

/-- 概要：二つの正方形の三角形の対角面は同じ対角の辺。
方針：Yoneda で有限順序写像の計算へ帰着する。
規約：どちらも中間面 δ₁。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の pushout の可換性。 -/
lemma squareTriangle_diagonal (i : Fin 2) :
    stdSimplex.δ (1 : Fin 3) ≫ squareTriangle.{u} i = squareDiagonal := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext
  all_goals fin_cases i <;> decide

/-- 概要：正方形の二つの三角形の交わりは対角の辺。
方針：標準単体の積の単体が生成する部分複体の包含を頂点写像の像の包含で判定する。
規約：部分複体の等式を全次数で示す。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の正方形の pushout。 -/
lemma squareTriangle_inf :
    Subcomplex.ofSimplex (squareTriangleSimplex.{u} 0).val ⊓
      Subcomplex.ofSimplex (squareTriangleSimplex 1).val =
        Subcomplex.ofSimplex squareDiagonalSimplex.val := by
  ext ⟨⟨n⟩⟩ s
  change (s ∈ (Subcomplex.ofSimplex (squareTriangleSimplex 0).val).obj _ ∧
    s ∈ (Subcomplex.ofSimplex (squareTriangleSimplex 1).val).obj _) ↔ _
  rw [← Subcomplex.ofSimplex_le_iff s, ← Subcomplex.ofSimplex_le_iff s,
    ← Subcomplex.ofSimplex_le_iff s]
  rw [prodStdSimplex.ofSimplex_le_ofSimplex_iff, prodStdSimplex.ofSimplex_le_ofSimplex_iff,
    prodStdSimplex.ofSimplex_le_ofSimplex_iff, ← Set.subset_inter_iff]
  have hr : Set.range (prodStdSimplex.objEquiv.{u} (squareTriangleSimplex.{u} 0).val) ∩
      Set.range (prodStdSimplex.objEquiv.{u} (squareTriangleSimplex.{u} 1).val) =
        Set.range (prodStdSimplex.objEquiv.{u} squareDiagonalSimplex.{u}.val) := by
    ext ⟨i, j⟩
    simp only [Set.mem_inter_iff, Set.mem_range]
    fin_cases i <;> fin_cases j <;> decide
  rw [hr]

/-- 概要：正方形の二つの三角形の和は正方形全体。
方針：二次元の非退化単体を Mathlib の列挙で尽くし、最大次元の単体による生成を使う。
規約：退化単体も含む部分複体の等式。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の正方形の pushout。 -/
lemma squareTriangle_sup :
    Subcomplex.ofSimplex (squareTriangleSimplex.{u} 0).val ⊔
      Subcomplex.ofSimplex (squareTriangleSimplex 1).val = ⊤ := by
  apply (prodStdSimplex.subcomplex_eq_top_iff _ rfl).2
  intro s hs
  obtain ⟨i, hi⟩ := prodStdSimplex₁.nonDegenerateEquiv.surjective ⟨s, hs⟩
  have he : (squareTriangleSimplex i).val = s := congrArg Subtype.val hi
  rw [← he]
  fin_cases i
  · exact Or.inl (Subcomplex.mem_ofSimplex_obj _)
  · exact Or.inr (Subcomplex.mem_ofSimplex_obj _)

/-- 概要：非退化単体による標準単体とその像の同型。
方針：単射な Yoneda 射の像への射は同型であることを使う。
規約：標的は二つの標準単体の積の中の部分複体。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の三角形の標準表示。 -/
noncomputable def prodSimplexImageIso {p q n : ℕ}
    (s : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n) :
    (Δ[n] : SSet.{u}) ≅ (Subcomplex.ofSimplex s.val : SSet.{u}) := by
  haveI := mono_yoneda_prod_nonDegenerate s
  haveI := (Subcomplex.isIso_toOfSimplex_iff s.val).2 inferInstance
  exact asIso (Subcomplex.toOfSimplex s.val)

/-- 概要：正方形は対角の辺に沿った二つの三角形の pushout。
方針：像の部分複体の交わりと和を計算し、標準単体の表示同型で移送する。
規約：共通の辺は両三角形の δ₁ の面。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の cospan の錐との比較。 -/
lemma square_isPushout : IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
    (squareTriangle.{u} 0) (squareTriangle 1) := by
  have hs : Subcomplex.BicartSq (Subcomplex.ofSimplex squareDiagonalSimplex.val)
      (Subcomplex.ofSimplex (squareTriangleSimplex.{u} 0).val)
      (Subcomplex.ofSimplex (squareTriangleSimplex 1).val) ⊤ :=
    ⟨squareTriangle_sup, squareTriangle_inf⟩
  apply hs.isPushout.of_iso' (prodSimplexImageIso squareDiagonalSimplex)
    (prodSimplexImageIso (squareTriangleSimplex 0))
    (prodSimplexImageIso (squareTriangleSimplex 1)) (Subcomplex.topIso _).symm
  · apply (cancel_mono (Subcomplex.ofSimplex (squareTriangleSimplex 0).val).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, prodSimplexImageIso,
      asIso_hom, Subcomplex.toOfSimplex_ι]
    exact (squareTriangle_diagonal 0).symm
  · apply (cancel_mono (Subcomplex.ofSimplex (squareTriangleSimplex 1).val).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, prodSimplexImageIso,
      asIso_hom, Subcomplex.toOfSimplex_ι]
    exact (squareTriangle_diagonal 1).symm
  · apply (cancel_mono (⊤ : (Δ[1] ⊗ Δ[1] : SSet.{u}).Subcomplex).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, prodSimplexImageIso,
      asIso_hom, Subcomplex.toOfSimplex_ι]
    rfl
  · apply (cancel_mono (⊤ : (Δ[1] ⊗ Δ[1] : SSet.{u}).Subcomplex).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, prodSimplexImageIso,
      asIso_hom, Subcomplex.toOfSimplex_ι]
    rfl

/-- 概要：cospan の錐の、零番目の脚を含む三角形。
方針：Δ[0]⋆Δ[1] の同型を使ってホーンの辺の包含を join する。
規約：頂点は錐頂点、cospan の 0、cospan の 2。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の引き戻しの正方形。 -/
def cospanConeTriangleLeft : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] (horn 2 2 : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) horn₂₂.ι₀₂

/-- 概要：cospan の錐の、一番目の脚を含む三角形。
方針：Δ[0]⋆Δ[1] の同型を使ってホーンの辺の包含を join する。
規約：頂点は錐頂点、cospan の 1、cospan の 2。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の引き戻しの正方形。 -/
def cospanConeTriangleRight : (Δ[2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] (horn 2 2 : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) horn₂₂.ι₁₂

/-- 概要：cospan の錐は共通の対角の辺に沿った二つの標準三角形の pushout。
方針：ホーンと join の pushout を標準単体の join の同型で移送する。
規約：両三角形の共通の辺は δ₁。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の正方形との比較。 -/
lemma cospanCone_isPushout : IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
    cospanConeTriangleLeft.{u} cospanConeTriangleRight := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRight_horn₂₂_isPushout (Δ[0] : SSet.{u})).of_iso'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).symm (Iso.refl _)
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one (0 : Fin 2), Iso.inv_hom_id_assoc]
    rfl
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one (0 : Fin 2), Iso.inv_hom_id_assoc]
    rfl
  · rfl
  · rfl

/-- 概要：cospan の錐 Δ[0]⋆Λ[2,2] は正方形 Δ[1]⊗Δ[1] と同型。
方針：対角に沿う二つの三角形の pushout の普遍性を両側で使う。
規約：錐頂点は (0,0)、ホーンの 0 は (1,0)、1 は (0,1)、2 は (1,1)。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の引き戻し四角形。 -/
noncomputable def cospanConeSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}) ≅ Δ[1] ⊗ Δ[1] :=
  cospanCone_isPushout.isoIsPushout _ _ square_isPushout.flip

/-- 概要：cospan の零番目の脚の錐三角形は正方形の下側三角形に写る。
方針：pushout を比較する同型の包含との整合性を使う。
規約：正方形の三角形の番号は 1。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の cospan の制限の向き。 -/
lemma cospanConeSquareIso_left :
    cospanConeTriangleLeft ≫ cospanConeSquareIso.{u}.hom = squareTriangle 1 :=
  cospanCone_isPushout.inl_isoIsPushout_hom _ _ _

/-- 概要：cospan の一番目の脚の錐三角形は正方形の上側三角形に写る。
方針：pushout を比較する同型の包含との整合性を使う。
規約：正方形の三角形の番号は 0。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の cospan の制限の向き。 -/
lemma cospanConeSquareIso_right :
    cospanConeTriangleRight ≫ cospanConeSquareIso.{u}.hom = squareTriangle 0 :=
  cospanCone_isPushout.inr_isoIsPushout_hom _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
