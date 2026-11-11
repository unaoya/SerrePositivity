module
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeActionInput
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeSequence

/-!
概要：同じ全高次懸垂作用から、各反復段の固定 K と native loop の全入力族を作る。
方針：元の S 作用・固定 K・元の native loop を同じ回数だけ合成する。
規約：採用済みの明示全高次作用に条件付き。段間の構造辺の自然性は別工程。
使われ方：K-7 c4・c5 の各段の全高次作用と元の点ごとの BF 列の厳密照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance nativeStageFamilySimplicialCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (a : DGSuspensionNativeActionInput R s)

/-- 概要：明示全高次懸垂作用に条件付きで、同じ第 n 段の全入力 K 作用を構成する。
方針：同じ n 回の懸垂・固定 K・n 回の native loop を合成する。
規約：入力射の厳密な恒等・合成の追加仮定を使わず、段間の β はまだ含めない。
使われ方：同じ非連結化候補の各段を全入力へ作用させる。 -/
def dgSuspensionNativeStageFamily (n : ℕ) :
    dgKInputInfinity.{u, max (u + 1) v} R ⟶ Sp.{max (u + 1) v} :=
  DGSuspensionNativeActionInput.iteration R s a n ≫ dgKInputK R ≫
    (End.of OmegaSpectrum.nativeLoop ^ n).asHom

/-- 概要：明示全高次作用に条件付きで、各段の全族の元の頂点は既存の同じ BF 列の頂点。
方針：元の反復作用と固定 K の頂点回収を順に適用する。
規約：段別入力や spectrum 模型を選び直さない。
使われ方：全入力族と元の各入力 A の非連結化列の厳密照合。 -/
theorem dgSuspensionNativeStageFamily_vertex
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    (dgSuspensionNativeStageFamily R s a n).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = dgSuspensionNativeSequenceVertex R s A n := by
  change ((End.of OmegaSpectrum.nativeLoop ^ n).asHom).app (Opposite.op ⦋0⦌)
    ((dgKInputK R).app (Opposite.op ⦋0⦌)
      ((DGSuspensionNativeActionInput.iteration R s a n).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A))) = _
  rw [DGSuspensionNativeActionInput.iteration_vertex, dgKInputK_vertex]
  rfl

/-- 概要：明示全高次作用に条件付きで、各元の dg 射の像は同じ反復 BF 射の loop 像。
方針：反復作用と固定 K の元の全一単体回収を使う。
規約：辺をホモトピー類だけに弱めず、元の全一単体を保持する。
使われ方：各段の全入力作用と既存の dg 入力射作用の照合。 -/
theorem dgSuspensionNativeStageFamily_edge
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (n : ℕ) :
    (dgSuspensionNativeStageFamily R s a n).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
    ((End.of OmegaSpectrum.nativeLoop ^ n).asHom).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSpectrumMap R
        (dgSuspensionIterationMap R s a.data f n))).edge := by
  change ((End.of OmegaSpectrum.nativeLoop ^ n).asHom).app (Opposite.op ⦋1⦌)
    ((dgKInputK R).app (Opposite.op ⦋1⦌)
      ((DGSuspensionNativeActionInput.iteration R s a n).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)) = _
  rw [DGSuspensionNativeActionInput.iteration_edge, dgKInputK_edge]

/-- 概要：明示全高次作用に条件付きで、反復懸垂の次段は同じ元の作用の前合成でも得られる。
方針：同じ作用の反復の結合だけを帰納的に読み替える。
規約：別の段別入力関手は選ばない。
使われ方：元の全 K 段族の再帰式。 -/
theorem DGSuspensionNativeActionInput.iteration_succ_left (n : ℕ) :
    DGSuspensionNativeActionInput.iteration R s a (n + 1) =
      a.map ≫ DGSuspensionNativeActionInput.iteration R s a n := by
  induction n with
  | zero =>
    change (𝟙 _ ≫ a.map) = a.map ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  | succ n ih =>
    change DGSuspensionNativeActionInput.iteration R s a (n + 1) ≫ a.map =
      a.map ≫ (DGSuspensionNativeActionInput.iteration R s a n ≫ a.map)
    rw [ih, Category.assoc]

/-- 概要：明示全高次作用に条件付きで、零段の全入力族は元の固定 K そのもの。
方針：零回の懸垂と loop の恒等を消去する。
規約：元の連結 K を別の模型へ置換しない。
使われ方：K-7 d1 の元の連結 K の始点を全入力で保持する。 -/
theorem dgSuspensionNativeStageFamily_zero :
    dgSuspensionNativeStageFamily R s a 0 = dgKInputK R := by
  change (𝟙 _ ≫ dgKInputK R ≫ 𝟙 _) = dgKInputK R
  rw [Category.id_comp, Category.comp_id]

/-- 概要：明示全高次作用に条件付きで、次段の全入力族は同じ懸垂と native loop に厳密に従う。
方針：同じ反復作用の左再帰式と native loop の冪の結合を使う。
規約：全単体上の等式であり、段間の構造辺の存在や自然性は主張しない。
使われ方：K-7 c5 の同じ全入力段族の構造射を照合するための再帰式。 -/
theorem dgSuspensionNativeStageFamily_succ (n : ℕ) :
    dgSuspensionNativeStageFamily R s a (n + 1) =
      a.map ≫ dgSuspensionNativeStageFamily R s a n ≫ OmegaSpectrum.nativeLoop := by
  simp only [dgSuspensionNativeStageFamily,
    DGSuspensionNativeActionInput.iteration_succ_left, pow_succ', End.mul_asHom, Category.assoc]

end SerrePositivity.KST.NonConnective
