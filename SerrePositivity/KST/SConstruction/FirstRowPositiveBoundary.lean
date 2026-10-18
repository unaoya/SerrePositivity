module
public import SerrePositivity.KST.SConstruction.FramePreservingCompletion
public import SerrePositivity.KST.SConstruction.FirstRowCofiberData

/-! # 第一行制限の正次元の相対境界充填
概要：指定する部分が全頂点を含むとき、第一行制限は厳密な相対持ち上げを持つ。
方針：境界と枠を同時に固定する cofiber 補完と、全部分複体の頂点条件を合わせる。
規約：零次元の存在は別問題として残す。使われ方：BGT Lemma 7.3、HTT §4.3.2。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：第一行の相対補完データは、枠上の cofiber 族も保つよう選べる。
方針：枠を先に補い、相対内部 Hom で cofiber の補完だけを選び直す。
規約：未証明の条件を仮定する構造体は追加しない。
使われ方：第一行制限の厳密な境界持ち上げ。 -/
lemma exists_firstRowCofiberData_preserving_frame {A B C : SSet.{u}}
    [Quasicategory C] [IsStable C] (n : ℕ) (i : A ⟶ B) [Mono i]
    (a : A ⟶ sConstruction n C) (d : B ⟶ (ihom (firstRowNerve n)).obj C)
    (h : a ≫ firstRowRestriction n C = i ≫ d) :
    ∃ c : FirstRowCofiberData n i a d,
      c.cofibers.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) =
        c.frame ≫ zeroFrameCofiberFamiliesMap n C := by
  let c := firstRowCofiberData n i a d h
  obtain ⟨f, hf⟩ := exists_arCofiberCompletion_preserving_frame n i a c.frame c.frame_boundary.symm
  exact ⟨{ c with cofibers := f }, hf⟩

/-- 概要：全頂点を含む相対補完は S_n に持ち上げた後も枠全体を保つ。
方針：枠の全部分複体への包含後で cofiber 族の右上角の回収を使う。
規約：枠上の cofiber 族を保つ条件を明記する。
使われ方：出力の第一行の指定入力との厳密な一致。 -/
lemma FirstRowCofiberData.toGapped_frame {A B C : SSet.{u}} [Quasicategory C]
    {n : ℕ} {i : A ⟶ B} {a : A ⟶ sConstruction n C}
    {d : B ⟶ (ihom (firstRowNerve n)).obj C} (c : FirstRowCofiberData n i a d)
    (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌)))
    (hc : c.cofibers.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) =
      c.frame ≫ zeroFrameCofiberFamiliesMap n C) :
    c.toGapped hi ≫ gappedFrameRestriction n C = c.frame := by
  apply (cancel_mono (fullSubcomplexOnVertices _ IsZeroFrameVertex).ι).1
  rw [Category.assoc, gappedFrameRestriction_ι, ← Category.assoc, c.toGapped_ι]
  exact c.cofibers.diagram_frame hc

/-- 概要：全頂点を含む部分からの枠を保つ補完の第一行は指定入力に厳密に等しい。
方針：第一行制限を枠への制限で因子分解する。
規約：ホモトピー等号には弱めない。使われ方：境界 RLP の右側の条件。 -/
lemma FirstRowCofiberData.toGapped_firstRow {A B C : SSet.{u}} [Quasicategory C]
    {n : ℕ} {i : A ⟶ B} {a : A ⟶ sConstruction n C}
    {d : B ⟶ (ihom (firstRowNerve n)).obj C} (c : FirstRowCofiberData n i a d)
    (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌)))
    (hc : c.cofibers.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) =
      c.frame ≫ zeroFrameCofiberFamiliesMap n C) :
    c.toGapped hi ≫ firstRowRestriction n C = d := by
  rw [← firstRowRestriction_factor, ← Category.assoc, c.toGapped_frame hi hc, c.firstRow]

/-- 概要：第一行制限は全頂点を含む任意の単射に対して持ち上げ性を持つ。
方針：枠を保つ cofiber データを実際に構成し、gapped 性と両側の等号を確認する。
規約：C は安定な quasicategory。使われ方：正次元の全境界での充填。 -/
lemma firstRowRestriction_hasLiftingProperty_of_vertexSurjective {A B C : SSet.{u}}
    [Quasicategory C] [IsStable C] (n : ℕ) (i : A ⟶ B) [Mono i]
    (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) :
    HasLiftingProperty i (firstRowRestriction n C) := by
  constructor
  intro a d sq
  obtain ⟨c, hc⟩ := exists_firstRowCofiberData_preserving_frame n i a d sq.w
  exact CommSq.HasLift.mk' {
    l := c.toGapped hi
    fac_left := c.toGapped_boundary hi
    fac_right := c.toGapped_firstRow hi hc }

/-- 概要：第一行制限は正次元の全ての標準境界を持ち上げる。
方針：正次元の境界が全頂点を含むことを適用する。
規約：零次元の持ち上げはこの定理には含めない。
使われ方：第一行制限の trivial Kan fibration の正次元部分。 -/
lemma firstRowRestriction_hasLiftingProperty_boundary (n r : ℕ) (C : SSet.{u})
    [Quasicategory C] [IsStable C] :
    HasLiftingProperty (boundary (r + 1)).ι (firstRowRestriction n C) :=
  firstRowRestriction_hasLiftingProperty_of_vertexSurjective n _ (boundary_vertex_surjective r)

end SerrePositivity.KST.SConstruction
