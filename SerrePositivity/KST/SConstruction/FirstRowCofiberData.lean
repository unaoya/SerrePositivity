module
public import SerrePositivity.KST.SConstruction.ArCofiberCompletion

/-! # 第一行を指定した相対 cofiber 補完のデータ
概要：第一行と既存の gapped 境界から、零対角の枠と Ar[n] 上の cofiber 族を構成する。
方針：枠の射影と cofiber の射影の trivial Kan fibration を順に持ち上げる。
規約：出力図式の gapped 性と第一行との一致の証明はこのデータと区別する。
使われ方：第一行制限の全境界持ち上げの構成部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定した第一行を持つ零対角の枠と、その相対 cofiber 補完。
方針：枠の第一行・境界の等号と、実際の cofiber の族を保持する。
規約：gapped 性や出力の第一行を未証明のフィールドとして仮定しない。
使われ方：第一行復元の残る二条件を検証するための構成済み入力。 -/
structure FirstRowCofiberData {A B C : SSet.{u}} (n : ℕ) (i : A ⟶ B)
    (a : A ⟶ sConstruction n C) (d : B ⟶ (ihom (firstRowNerve n)).obj C) where
  frame : B ⟶ zeroFrameDiagrams n C
  frame_boundary : i ≫ frame = a ≫ gappedFrameRestriction n C
  firstRow : frame ≫ frameRowRestriction n C = d
  cofibers : ArCofiberCompletion n i a frame

/-- 概要：任意の単射上の gapped 図式と全体の第一行から相対 cofiber データを構成できる。
方針：零対角の枠を第一行の上で持ち上げ、Ar[n] 全体の cofiber を境界を固定して補完する。
規約：C は安定な quasicategory、i は任意の単射。
使われ方：第一行制限の境界持ち上げの実際の補完データ。 -/
def firstRowCofiberData {A B C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (n : ℕ) (i : A ⟶ B) [Mono i] (a : A ⟶ sConstruction n C)
    (d : B ⟶ (ihom (firstRowNerve n)).obj C) (h : a ≫ firstRowRestriction n C = i ≫ d) :
    FirstRowCofiberData n i a d := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := frameRowRestriction n C) i inferInstance
  have sq : CommSq (a ≫ gappedFrameRestriction n C) i (frameRowRestriction n C) d := by
    constructor
    rw [Category.assoc, firstRowRestriction_factor]
    exact h
  exact ⟨sq.lift, sq.fac_left, sq.fac_right, arCofiberCompletion n i a sq.lift sq.fac_left.symm⟩

/-- 概要：第一行から構成した補完の右上角は全体上の Ar[n] 図式の族を与える。
方針：相対 cofiber データの右上角を取る。
規約：この定義では S_n への持ち上げをまだ主張しない。
使われ方：gapped 条件と第一行の回収を検証する出力の候補。 -/
def FirstRowCofiberData.diagram {A B C : SSet.{u}} {n : ℕ} {i : A ⟶ B}
    {a : A ⟶ sConstruction n C} {d : B ⟶ (ihom (firstRowNerve n)).obj C}
    (c : FirstRowCofiberData n i a d) : B ⟶ (ihom (arNerve n)).obj C := c.cofibers.diagram

/-- 概要：第一行から構成した補完は指定した gapped 境界を厳密に回収する。
方針：相対 cofiber 補完の境界の回収の等号を使う。
規約：任意の高次パラメーターに対して成立。
使われ方：第一行制限の境界持ち上げの左側の条件。 -/
lemma FirstRowCofiberData.diagram_boundary {A B C : SSet.{u}} {n : ℕ} {i : A ⟶ B}
    {a : A ⟶ sConstruction n C} {d : B ⟶ (ihom (firstRowNerve n)).obj C}
    (c : FirstRowCofiberData n i a d) : i ≫ c.diagram = a ≫ (gappedSubcomplex n C).ι :=
  c.cofibers.diagram_boundary

/-- 概要：全頂点を含む指定部分を保つ補完の各頂点は gapped である。
方針：頂点を指定部分から持ち上げ、境界の厳密な回収の等号を使う。
規約：i の零次成分の全射性を明記する。使われ方：正次元の境界の場合の gapped 条件。 -/
lemma FirstRowCofiberData.diagram_isGapped_of_vertexSurjective {A B C : SSet.{u}}
    {n : ℕ} {i : A ⟶ B} {a : A ⟶ sConstruction n C} {d : B ⟶ (ihom (firstRowNerve n)).obj C}
    (c : FirstRowCofiberData n i a d) (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌)))
    (v : B _⦋0⦌) : IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm
      (c.diagram.app (Opposite.op ⦋0⦌) v)) := by
  obtain ⟨u, hu⟩ := hi v
  have hh := ConcreteCategory.congr_hom (NatTrans.congr_app c.diagram_boundary (Opposite.op ⦋0⦌)) u
  change c.diagram.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) u) =
    (a.app (Opposite.op ⦋0⦌) u).val at hh
  rw [hu] at hh
  rw [hh]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) u)

/-- 概要：全頂点を含む部分からの cofiber 補完は S_n(C) に持ち上がる。
方針：全頂点の gapped 条件で全部分複体へ持ち上げる。
規約：第一行の回収の等号はまだこの定義に含めない。
使われ方：正次元の境界での第一行制限の持ち上げ。 -/
def FirstRowCofiberData.toGapped {A B C : SSet.{u}} {n : ℕ} {i : A ⟶ B}
    {a : A ⟶ sConstruction n C} {d : B ⟶ (ihom (firstRowNerve n)).obj C}
    (c : FirstRowCofiberData n i a d) (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) :
    B ⟶ sConstruction n C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ c.diagram (c.diagram_isGapped_of_vertexSurjective hi)

/-- 概要：S_n に持ち上げた補完の図式は元の右上角の図式。
方針：全部分複体の持ち上げの包含後の式。
規約：厳密等号。使われ方：指定した境界の回収。 -/
lemma FirstRowCofiberData.toGapped_ι {A B C : SSet.{u}} {n : ℕ} {i : A ⟶ B}
    {a : A ⟶ sConstruction n C} {d : B ⟶ (ihom (firstRowNerve n)).obj C}
    (c : FirstRowCofiberData n i a d) (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) :
    c.toGapped hi ≫ (gappedSubcomplex n C).ι = c.diagram := rfl

/-- 概要：全頂点を含む部分で指定した S_n の図式は補完後も厳密に一致する。
方針：全部分複体の包含後で元の図式の境界の等号を使う。
規約：第一行の右側の等号と区別する。使われ方：正次元の持ち上げの左側の条件。 -/
lemma FirstRowCofiberData.toGapped_boundary {A B C : SSet.{u}} {n : ℕ} {i : A ⟶ B}
    {a : A ⟶ sConstruction n C} {d : B ⟶ (ihom (firstRowNerve n)).obj C}
    (c : FirstRowCofiberData n i a d) (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) :
    i ≫ c.toGapped hi = a := by
  apply (cancel_mono (gappedSubcomplex n C).ι).1
  rw [Category.assoc, c.toGapped_ι hi, c.diagram_boundary]

/-- 概要：正次元の標準単体の全頂点は境界に含まれる。
方針：標準頂点と零単体の同値で境界の頂点包含を読む。
規約：r+1 次元を扱う。使われ方：指定した gapped 境界からの頂点条件の回収。 -/
lemma boundary_vertex_surjective (r : ℕ) :
    Function.Surjective ((boundary.{u} (r + 1)).ι.app (Opposite.op ⦋0⦌)) := by
  intro v
  refine ⟨⟨v, ?_⟩, rfl⟩
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} r (stdSimplex.obj₀Equiv.{u} v)
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- 概要：第一行の充填を持つ正次元の gapped 境界は、全図式として充填できる。
方針：枠と cofiber の相対補完を構成し、全頂点が境界にあることから gapped 性を得る。
規約：得られた図式の第一行が指定充填に一致する等号は、この補題の結論には含めない。
使われ方：第一行制限の持ち上げのうち、左側の境界条件と gapped 条件。 -/
lemma exists_gappedBoundaryFilling_of_firstRowFilling (n r : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (a : (boundary (r + 1) : SSet.{u}) ⟶ sConstruction n C)
    (d : (Δ[r + 1] : SSet.{u}) ⟶ (ihom (firstRowNerve n)).obj C)
    (h : a ≫ firstRowRestriction n C = (boundary (r + 1)).ι ≫ d) :
    ∃ F : (Δ[r + 1] : SSet.{u}) ⟶ sConstruction n C, (boundary (r + 1)).ι ≫ F = a := by
  let c := firstRowCofiberData n (boundary (r + 1)).ι a d h
  exact ⟨c.toGapped (boundary_vertex_surjective r), c.toGapped_boundary (boundary_vertex_surjective r)⟩

end SerrePositivity.KST.SConstruction
