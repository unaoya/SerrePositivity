module

public import SerrePositivity.KST.Spectra.KanEquivalenceBridge

/-!
概要：参照頂点を持つ Kan 複体の全基点 π_* 同型の前側の消去。
方針：頂点の像で基点を付け、実際の Whitehead 逆を通じて合成の消去則を使う。
規約：始域の頂点を明示し、空な始域での全基点条件の空虚性を避ける。
使われ方：Goerss–Jardine I §7、VII §4、VIII §1。Reedy 因子分解の二射影の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：頂点の像で基点を選んだ単体集合の実際の点つき射。
方針：定数射の後合成の公式で基点保存を示す。
規約：Kan 性は不要。
使われ方：Goerss–Jardine I §7。参照頂点から Whitehead の点つき版への接続。 -/
def pointedMapAtVertex {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    PointedSimplicialSet.ofVertex X x ⟶ PointedSimplicialSet.ofVertex Y (f.app _ x) :=
  Under.homMk f (by
    change SSet.const x ≫ f = SSet.const (f.app _ x)
    rw [SSet.const_comp])

/-- 概要：参照頂点を持つ Kan 複体の全基点 π_* 同型は実際の単体的ホモトピー同値。
方針：基点を頂点の像へ送り、本レーンの点つき Whitehead の逆を使う。
規約：逆射の存在は Lean 内で構成済みの Whitehead による。
使われ方：Goerss–Jardine I §7、Kerodon 4.8.4.1（Tag 01JX）。合成の前側の消去。 -/
lemma kanPiIsomorphism_homotopyEquivalence_atVertex
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  let : KanComplex (PointedSimplicialSet.ofVertex X x).right :=
    inferInstanceAs (KanComplex X)
  let : KanComplex (PointedSimplicialSet.ofVertex Y (f.app _ x)).right :=
    inferInstanceAs (KanComplex Y)
  exact pointed_piIsomorphism_homotopyEquivalence (pointedMapAtVertex f x) hf

/-- 概要：前の射と合成が全基点 π_* 同型なら、後の射も全基点 π_* 同型。
方針：参照頂点からの実際のホモトピー同値へ移し、合成の前側を消去する。
規約：始域の頂点が必要。零次数の成分集合も含む。
使われ方：Goerss–Jardine I §7、VII §4、VIII §1。因子分解の射影の同型性。 -/
lemma KanPiIsomorphism.cancel_left_atVertex
    {X Y Z : SSet.{u}} [KanComplex X] [KanComplex Y] [KanComplex Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) (hfg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f ≫ g)) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g :=
  kanPiIsomorphism_of_qCatEquivalence g
    ((kanPiIsomorphism_homotopyEquivalence_atVertex f hf x).isQCatEquivalence.cancel_left
      (kanPiIsomorphism_homotopyEquivalence_atVertex (f ≫ g) hfg x).isQCatEquivalence)

end

end SerrePositivity.KST.Spectra
