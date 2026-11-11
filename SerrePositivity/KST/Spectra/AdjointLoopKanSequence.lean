module

public import SerrePositivity.KST.Spectra.OrdinaryLoopAdjointStructureCriterion

/-!
概要：通常円の随伴構造射をそのまま loop で写す補助 Kan 列を作る。
方針：各段を通常 loop とし、随伴構造射の後合成を新しい随伴構造射とする。
規約：BF の単射置換と nativeLoop との全図式比較は後続工程で行う。
使われ方：d3 の一段移動と厳密随伴単位の自然性を、選択した Kan 持ち上げから分ける。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 概要：元の厳密な列の射は、通常円への随伴構造射とも厳密に可換。
方針：元の構造可換式を curry する。
規約：射はホモトピー類へ移さない。
使われ方：補助 loop 列の射への作用。 -/
lemma ordinaryStructureAdjoint_natural {X Y : KanSequence.{u}} (f : X ⟶ Y) (n : ℕ) :
    f.app n ≫ ordinaryStructureAdjoint Y n =
      ordinaryStructureAdjoint X n ≫
        (ihom PointedSimplicialSet.circle.{u}).map (f.app (n + 1)) := by
  have hf := congrArg MonoidalClosed.curry (f.comm n)
  rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_natural_right] at hf
  exact hf

/-- 概要：随伴構造射を通常 loop の関手で写した補助 Kan 列。
方針：loop を取った段と、loop を取った随伴構造射を uncurry して束ねる。
規約：通常 cotensor 列との同定はこの定義に含めない。
使われ方：一段移動からの厳密な構造随伴単位。 -/
def adjointLoop (X : KanSequence.{u}) : KanSequence.{u} where
  level n := (mapping PointedSimplicialSet.circle X).level n
  sigma n := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _).symm
    ((ihom PointedSimplicialSet.circle.{u}).map (ordinaryStructureAdjoint X n))

/-- 概要：補助列の随伴構造射は元の随伴構造射の通常 loop。
方針：随伴の往復式を使う。
規約：厳密な点つき射の等式。
使われ方：Ω 条件と単位の構造可換性。 -/
@[simp] lemma adjointLoop_ordinaryStructureAdjoint (X : KanSequence.{u}) (n : ℕ) :
    ordinaryStructureAdjoint (adjointLoop X) n =
      (ihom PointedSimplicialSet.circle.{u}).map (ordinaryStructureAdjoint X n) :=
  Equiv.apply_symm_apply _ _

/-- 概要：元の Ω 条件は補助 loop 列で保存される。
方針：通常円からの内部 Hom が全基点 π 同型を保つことを適用する。
規約：構造射の単射性はこの段階では要求しない。
使われ方：後続の BF 単射置換への実入力。 -/
lemma adjointLoop_omegaCondition {X : KanSequence.{u}} (hX : X.OmegaCondition) :
    (adjointLoop X).OmegaCondition := by
  intro n
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (ordinaryStructureAdjoint (adjointLoop X) n).right
  rw [adjointLoop_ordinaryStructureAdjoint]
  exact PointedMapping.post_piIsomorphism PointedSimplicialSet.circle _ (hX n)

/-- 概要：元の構造随伴は、一段移動した補助 loop 列への厳密な列の射。
方針：補助列の定義により二つの構造可換経路が同じ合成になる。
規約：段ごとのホモトピー選択を使わない。
使われ方：d3 の全関手比較へ接続する単位の前段。 -/
def adjointLoopTailUnit (X : KanSequence.{u}) : X ⟶ adjointLoop (tail X) :=
  Hom.ofAdjoint (ordinaryStructureAdjoint X) (fun n => by
    change ordinaryStructureAdjoint X n ≫ ordinaryStructureAdjoint (adjointLoop (tail X)) n =
      ordinaryStructureAdjoint X n ≫ (ihom PointedSimplicialSet.circle.{u}).map
        (ordinaryStructureAdjoint X (n + 1))
    rw [adjointLoop_ordinaryStructureAdjoint]
    rfl)

/-- 概要：補助 loop 列は、元の厳密な列の射を通常 loop の後合成で写す。
方針：構造随伴の自然性を通常 loop の関手で写す。
規約：各段の厳密な射と元の構造可換性を保つ。
使われ方：全関手比較の射への作用を固定する。 -/
def adjointLoopMap {X Y : KanSequence.{u}} (f : X ⟶ Y) :
    adjointLoop X ⟶ adjointLoop Y :=
  Hom.ofAdjoint (fun n => (ihom PointedSimplicialSet.circle.{u}).map (f.app n)) (fun n => by
    change (ihom PointedSimplicialSet.circle.{u}).map (f.app n) ≫
        ordinaryStructureAdjoint (adjointLoop Y) n =
      ordinaryStructureAdjoint (adjointLoop X) n ≫
        (ihom PointedSimplicialSet.circle.{u}).map
          ((ihom PointedSimplicialSet.circle.{u}).map (f.app (n + 1)))
    rw [adjointLoop_ordinaryStructureAdjoint, adjointLoop_ordinaryStructureAdjoint,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ordinaryStructureAdjoint_natural])

/-- 概要：補助 loop 列とその元の射への作用は厳密な関手となる。
方針：通常 loop の関手法則を各段へ適用する。
規約：coherent nerve 上の関手とは後続工程で比較する。
使われ方：BF 置換後の全関手比較の基礎データ。 -/
def adjointLoopFunctor : KanSequence.{u} ⥤ KanSequence.{u} where
  obj := adjointLoop
  map := adjointLoopMap
  map_id X := by
    apply Hom.ext_app
    intro n
    exact CategoryTheory.Functor.map_id (ihom PointedSimplicialSet.circle.{u}) _
  map_comp f g := by
    apply Hom.ext_app
    intro n
    exact CategoryTheory.Functor.map_comp (ihom PointedSimplicialSet.circle.{u}) _ _

/-- 概要：元の構造随伴からなる単位は、元の列の射に対して厳密に自然。
方針：元の構造随伴の自然性を列の外延性で束ねる。
規約：成分のホモトピー類に弱めない。
使われ方：一段移動と補助 loop の全関手比較への単位入力。 -/
lemma adjointLoopTailUnit_natural {X Y : KanSequence.{u}} (f : X ⟶ Y) :
    f ≫ adjointLoopTailUnit Y =
      adjointLoopTailUnit X ≫ adjointLoopMap (tailHom f) := by
  apply Hom.ext_app
  intro n
  exact ordinaryStructureAdjoint_natural f n

/-- 概要：Ω 列の厳密な構造随伴単位は、全段の全基点 π 同型。
方針：元の Ω 条件の射そのものを取り出す。
規約：元の射の定義を変えず、BF 置換の入力として使う。
使われ方：補助列との比較の同値性を放電する。 -/
lemma adjointLoopTailUnit_levelwise {X : KanSequence.{u}} (hX : X.OmegaCondition) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((adjointLoopTailUnit X).app n).right := hX n

end SerrePositivity.KST.Spectra.KanSequence
