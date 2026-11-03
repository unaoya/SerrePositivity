module
public import SerrePositivity.InfinityCategories.Stable.DiagramNestedCoslice
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorRightPair
public import SerrePositivity.InfinityCategories.Stable.CoslicePostcompTrivial
public import SerrePositivity.InfinityCategories.Stable.ColimitExistenceTransfer

/-! # 始対象の下の図式から始対象を忘れる

概要：始対象の下の図式の余錐は、始対象を忘れた図式の余錐と同じ普遍性を持つ。
方針：二重 coslice の同型と、始対象の coslice 射影の trivial Kan fibration 性を使う。
規約：元の図式と余錐の射の制限を厳密に計算する。使われ方：零始点の押し出しから二項余積へ移る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：展開した図式の下の coslice から最初の固定因子を忘れる。
方針：二重 coslice へ移し、内側の coslice 射影で後合成する。
規約：始対象性を仮定せず定義する。使われ方：零始点の枝の条件を除く射。 -/
def diagramNestedCosliceProjection {K L X : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) :
    sliceUnder (sliceUnderUncurry c) ⟶ sliceUnder (c ≫ sliceUnderProjection p) :=
  (diagramNestedCosliceIso c).hom ≫ sliceUnderPostcomp c (sliceUnderProjection p)

/-- 概要：二重 coslice の射の同値は比較同型での後合成である。
方針：パラメーターの自然性を恒等射に適用する。
規約：任意のパラメーターを許す。使われ方：射影の uncurry の式。 -/
lemma diagramNestedCosliceHomEquiv_eq_comp {K L X A : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) (f : A ⟶ sliceUnder (sliceUnderUncurry c)) :
    diagramNestedCosliceHomEquiv c A f = f ≫ (diagramNestedCosliceIso c).hom := by
  dsimp only [diagramNestedCosliceIso]
  simpa only [Category.comp_id] using diagramNestedCosliceHomEquiv_naturality c f (𝟙 _)

/-- 概要：最初の因子を忘れる射は、uncurry すると後の因子の包含による制限である。
方針：二重 uncurry の式と、結合同型の後二因子の包含の式を合わせる。
規約：射の厳密な等号。使われ方：余錐の脚と頂点を保持する比較。 -/
lemma diagramNestedCosliceProjection_uncurry {K L X A : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) (f : A ⟶ sliceUnder (sliceUnderUncurry c)) :
    sliceUnderUncurry (f ≫ diagramNestedCosliceProjection c) =
      joinMap (joinInr K L) (𝟙 A) ≫ sliceUnderUncurry f := by
  change sliceUnderUncurry ((f ≫ (diagramNestedCosliceIso c).hom) ≫
    sliceUnderPostcomp c (sliceUnderProjection p)) = _
  rw [sliceUnderUncurry_postcomp, ← sliceUnderUncurry_projection,
    ← diagramNestedCosliceHomEquiv_eq_comp, diagramNestedCosliceHomEquiv_doubleUncurry,
    ← Category.assoc, stableJoinAssociator_rightPair_inv]

/-- 概要：最初の固定因子を忘れた余錐の射は、後の因子の包含で元の余錐を制限した射である。
方針：射影の uncurry の式を零単体に適用する。
規約：固定条件の証明には依存しない。使われ方：二項余積の二本の脚の照合。 -/
lemma diagramNestedCosliceProjection_val {K L X : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) (d : JoinCocone (sliceUnderUncurry c)) :
    ((diagramNestedCosliceProjection c).app (Opposite.op ⦋0⦌) d).val =
      joinMap (joinInr K L) (𝟙 (Δ[0] : SSet.{u})) ≫ d.val := by
  have h := diagramNestedCosliceProjection_uncurry c (SSet.yonedaEquiv.symm d)
  rw [SSet.yonedaEquiv_symm_comp, sliceUnderUncurry_yoneda, sliceUnderUncurry_yoneda] at h
  exact h

/-- 概要：最初の固定因子を忘れても余錐の頂点は変わらない。
方針：余錐の射の制限の式と右包含の自然性を使う。
規約：実際の零単体の等号。使われ方：同じ余極限対象での二項余積の判定。 -/
lemma diagramNestedCosliceProjection_vertex {K L X : SSet.{u}} {p : K ⟶ X}
    (c : L ⟶ sliceUnder p) (d : JoinCocone (sliceUnderUncurry c)) :
    (show JoinCocone (c ≫ sliceUnderProjection p) from
      (diagramNestedCosliceProjection c).app (Opposite.op ⦋0⦌) d).vertex = d.vertex := by
  rw [JoinCocone.vertex_eq, JoinCocone.vertex_eq, diagramNestedCosliceProjection_val]
  rw [← Category.assoc, joinInr_joinMap, Category.id_comp]

/-- 概要：内側の coslice 射影が trivial なら最初の因子を忘れる射も trivial Kan fibration。
方針：後合成の trivial Kan fibration 性と二重 coslice の同型を合成する。
規約：値域の quasicategory 性は不要。使われ方：始対象の下の図式。 -/
lemma diagramNestedCosliceProjection_trivialKanFibration {K L X : SSet.{u}} {p : K ⟶ X}
    [TrivialKanFibration (sliceUnderProjection p)] (c : L ⟶ sliceUnder p) :
    TrivialKanFibration (diagramNestedCosliceProjection c) := by
  have h := sliceUnderPostcomp_trivialKanFibration_of_trivial c (sliceUnderProjection p)
  exact ⟨trivialKanFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _) h.mem⟩

/-- 概要：始対象の下の図式から始対象を忘れる射は trivial Kan fibration。
方針：始対象の coslice 射影の判定を使う。
規約：形状 L と値域は任意。使われ方：零始点の span の余錐の判定。 -/
lemma diagramNestedCosliceProjection_trivial_of_initial {L X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsInitialVertex x) (c : L ⟶ sliceUnder (SSet.yonedaEquiv.symm x)) :
    TrivialKanFibration (diagramNestedCosliceProjection c) := by
  have := (isInitialVertex_iff_trivialKanFibration x).1 hx
  exact diagramNestedCosliceProjection_trivialKanFibration c

/-- 概要：始対象の下で展開した図式の余錐は、始対象を忘れた余錐と余極限性が同値である。
方針：最初の因子を忘れる trivial Kan fibration の始対象性の保存・反映を使う。
規約：X は quasicategory、初めの頂点は始対象。使われ方：二項余積の余極限条件。 -/
lemma isColimitCone_iff_forget_initial {L X : SSet.{u}} [Quasicategory X] {x : X _⦋0⦌}
    (hx : IsInitialVertex x) (c : L ⟶ sliceUnder (SSet.yonedaEquiv.symm x))
    (d : JoinCocone (sliceUnderUncurry c)) :
    IsColimitCone d ↔
      IsColimitCone ((diagramNestedCosliceProjection c).app (Opposite.op ⦋0⦌) d) := by
  have := diagramNestedCosliceProjection_trivial_of_initial hx c
  exact (qCatEquivalenceOfTrivialKanFibration
    (diagramNestedCosliceProjection c)).isInitialVertex_iff d

end SerrePositivity.InfinityCategories
