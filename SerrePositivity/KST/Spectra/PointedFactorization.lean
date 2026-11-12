module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators

/-!
概要：点つき射の単射と全境界右持ち上げ射への分解。
方針：境界の小対象論法の中間対象に、左因子による基点を入れる。
規約：Kan–Quillen の弱同値クラスは使わず、右因子の π_* 同型性を実証する。
使われ方：BF 1978 §2、HTT A.3.3。cofibrant 置換の段ごとの充填の準備。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel

namespace SerrePositivity.KST.Spectra.PointedFactorization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：境界の小対象論法による単体集合の関手的分解。
方針：境界で生成される左クラスが単射である証明を使う。
規約：右クラスは全境界に対する RLP。
使われ方：BF 1978 §2、HTT A.3.3。点つき分解の基礎データ。 -/
def factorization : MorphismProperty.FunctorialFactorizationData
    (MorphismProperty.monomorphisms SSet.{u}) I.rlp := by
  rw [← boundaryGenerators_leftClass]
  let : I.{u}.HasSmallObjectArgument.{u} := boundaryGenerators_smallObjectArgument
  exact MorphismProperty.functorialFactorizationData _ _

/-- 概要：点つき射の分解の中間対象。
方針：元の基点を左因子で送った像を新しい基点とする。
規約：入力の両端に Kan 性は要求しない。
使われ方：BF 1978 §2、HTT A.3.3。cofibrant 置換の各段。 -/
def middle {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : PointedSimplicialSet.{u} :=
  Under.mk (X.hom ≫ factorization.i.app (Arrow.mk f.right))

/-- 概要：点つき分解の左因子。
方針：小対象論法の左因子を点つき射へ持ち上げる。
規約：基礎射は単射。
使われ方：BF 1978 §2、HTT A.3.3。構造射の単射化。 -/
def left {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : X ⟶ middle f :=
  Under.homMk (factorization.i.app (Arrow.mk f.right))

/-- 概要：点つき分解の右因子。
方針：分解の合成の等式と元の射の基点保存を使う。
規約：基礎射は全ての単射に対する RLP を持つ。
使われ方：BF 1978 §2、HTT A.3.3。元の段への比較射。 -/
def right {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : middle f ⟶ Y :=
  Under.homMk (factorization.p.app (Arrow.mk f.right)) (by
    change (X.hom ≫ factorization.i.app (Arrow.mk f.right)) ≫
      factorization.p.app (Arrow.mk f.right) = Y.hom
    rw [Category.assoc, factorization.fac_app]
    exact Under.w f)

/-- 概要：点つき分解の合成は元の射。
方針：基礎分解の合成の法則を使う。
規約：点つき射の厳密な等式。
使われ方：BF 1978 §2。スペクトルの構造射との可換性。 -/
@[reassoc (attr := simp)]
theorem fac {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : left f ≫ right f = f := by
  apply Under.UnderMorphism.ext
  exact factorization.fac_app

/-- 概要：左因子の基礎射は単射。
方針：境界の小対象論法の左クラスの性質を使う。
規約：点つき忘却後の射。
使われ方：BF 1978 §2。cofibrant な構造射の構成。 -/
instance left_mono {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : Mono (left f).right :=
  factorization.hi _

/-- 概要：右因子の基礎射は全ての単射に対する右持ち上げ性を持つ。
方針：境界の RLP が全ての単射の RLP と一致することを使う。
規約：相対 cell 分解の既存の定理による等式。
使われ方：BF 1978 §2、HTT A.3.3。比較射の π_* 保存。 -/
theorem right_rlp {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (right f).right := by
  rw [SSet.rlp_monomorphisms]
  exact factorization.hp _

/-- 概要：右因子の基礎射は Kan fibration。
方針：ホーン包含も単射であることを使う。
規約：両端の Kan 性には依存しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。中間対象の Kan 性。 -/
instance right_fibration {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    Fibration (right f).right :=
  (fibration_iff _).2 (fun _ _ g hg ↦ right_rlp f g (J_le_monomorphisms _ hg))

/-- 概要：標的が Kan なら中間対象も Kan。
方針：右因子と標的の終対象射という二つの fibration を合成する。
規約：左端に Kan 性を要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。段の Kan 性を保つ置換。 -/
instance middle_kanComplex {X Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (f : X ⟶ Y) : KanComplex (middle f).right := by
  change Fibration (terminal.from (middle f).right)
  rw [show terminal.from (middle f).right = (right f).right ≫ terminal.from Y.right from
    terminal.hom_ext _ _]
  infer_instance

/-- 概要：標的が Kan なら分解の右因子は全基点 π_* 同型。
方針：中間対象の Kan 性と全ての単射への RLP から構成済みのホモトピー逆を使う。
規約：零次数を含む全基点の比較。
使われ方：Goerss–Jardine I §7、BF 1978 §2。cofibrant 置換の段ごとの比較。 -/
theorem right_piIsomorphism {X Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (right f).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight (right f).right (right_rlp f)

end

end SerrePositivity.KST.Spectra.PointedFactorization
