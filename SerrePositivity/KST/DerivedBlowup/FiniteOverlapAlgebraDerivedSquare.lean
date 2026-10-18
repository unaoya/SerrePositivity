module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraDerivedComparison

/-!
概要：KST §3.1 の正規表示と Koszul 模型の導来制限の可換四角形。
方針：指定 dg 遷移の可換四角形へ標準導来制限合成同型を適用する。
規約：共通の合成 dg 関手を経由する指定自然同型を使う。
使われ方：局所表示変更に沿う係数拡大比較の随伴計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：元の局所導来加群圏から一対象正規表示への指定制限。
方針：Hom 恒等の dg 比較に沿う構成済み導来制限を使う。
規約：KST §3.1。使われ方：導来制限の可換四角形の縦辺。 -/
abbrev finiteOverlapAlgebraDerivedRestriction (a : I → R) (T : FiniteOverlapIndex I) :=
  dgDerivedRestriction R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
    (FiniteOverlapVertexObject R a T)ᵒᵖ (finiteOverlapAlgebraVertexToChart R a T).op

set_option maxHeartbeats 2000000 in
-- 二つの局所化環の導来制限の合成と正規表示を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の dg 構造を照合するために必要。
/-- 概要：局所遷移に沿う導来制限は一対象正規表示への制限と整合する。
方針：dg 可換四角形と二つの標準合成同型を接続する。
規約：KST §3.1。使われ方：二つの延長–制限随伴の比較。 -/
def finiteOverlapAlgebraDerivedRestrictionSquare (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    finiteOverlapDerivedTransitionRestriction R a h ⋙ finiteOverlapAlgebraDerivedRestriction R a T ≅
      finiteOverlapAlgebraDerivedRestriction R a U ⋙
        diagramAlgebraDerivedRestriction (finiteOverlapDGAlgebraDiagram R a) h :=
  transitionDerivedRestrictionCompIso (finiteOverlapAlgebraVertexToChart R a T)
      (finiteOverlapLocalDGTransition R a h)
      ((diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h).comp
        (finiteOverlapAlgebraVertexToChart R a U))
      (finiteOverlapAlgebraVertexToChart_transition R a h) ≪≫
    (transitionDerivedRestrictionCompIso
      (diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h)
      (finiteOverlapAlgebraVertexToChart R a U)
      ((diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h).comp
        (finiteOverlapAlgebraVertexToChart R a U)) rfl).symm

set_option maxHeartbeats 2000000 in
-- 局所化環の dg 比較に沿う制限合成同型を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の局所加群圏の構造を照合するために必要。
/-- 概要：可換四角形の元の遷移側の加群合成同型は恒等成分を持つ。
方針：標準合成同型の評価公式を一対象正規表示で計算する。
規約：KST §3.1。使われ方：導来可換四角形の成分計算。 -/
theorem finiteOverlapAlgebraRestrictionSquare_native_hom (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : ModuleCategory R (FiniteOverlapVertexObject R a U)ᵒᵖ) :
    (transitionRestrictionCompIso (finiteOverlapAlgebraVertexToChart R a T)
      (finiteOverlapLocalDGTransition R a h)
      ((diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h).comp
        (finiteOverlapAlgebraVertexToChart R a U))
      (finiteOverlapAlgebraVertexToChart_transition R a h)).hom.app M = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  rw [transitionRestrictionCompIso_eval, CategoryTheory.Functor.map_id]
  rfl

set_option maxHeartbeats 2000000 in
-- 正規表示の局所遷移と制限合成同型を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の局所加群圏の構造を照合するために必要。
/-- 概要：可換四角形の正規表示側の加群合成同型の逆成分は恒等。
方針：合成等式が反射律である標準同型の逆を評価する。
規約：KST §3.1。使われ方：導来可換四角形の逆側の成分計算。 -/
theorem finiteOverlapAlgebraRestrictionSquare_normal_inv (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : ModuleCategory R (FiniteOverlapVertexObject R a U)ᵒᵖ) :
    (transitionRestrictionCompIso
      (diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h)
      (finiteOverlapAlgebraVertexToChart R a U)
      ((diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h).comp
        (finiteOverlapAlgebraVertexToChart R a U)) rfl).inv.app M = 𝟙 _ := by
  apply moduleMorphism_ext
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  rw [CategoryTheory.Functor.map_id]
  change (moduleEvaluation R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ _).map
    (moduleRestrictionCompObjIso R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapAlgebraVertex R a U)ᵒᵖ (FiniteOverlapVertexObject R a U)ᵒᵖ
      (diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h).op.op
      (finiteOverlapAlgebraVertexToChart R a U).op.op M).inv = _
  exact moduleIsoMk_inv_eval R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ _ _ (Opposite.op .point)

set_option maxHeartbeats 2000000 in
-- 二つの局所化環を含む導来合成比較の成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の局所 dg 構造を照合するために必要。
/-- 概要：指定導来可換四角形の成分は各対象で恒等。
方針：実加群上の標準導来合成比較を計算し、恒等な加群成分へ戻す。
規約：KST §3.1。使われ方：指定導来制限比較の随伴四角形での照合。 -/
theorem finiteOverlapAlgebraDerivedRestrictionSquare_hom_app (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (X : DerivedModuleCategory R (FiniteOverlapVertexObject R a U)ᵒᵖ) :
    (finiteOverlapAlgebraDerivedRestrictionSquare R a h).hom.app X = 𝟙 _ := by
  change (transitionDerivedRestrictionCompIso (finiteOverlapAlgebraVertexToChart R a T)
      (finiteOverlapLocalDGTransition R a h)
      ((diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h).comp
        (finiteOverlapAlgebraVertexToChart R a U))
      (finiteOverlapAlgebraVertexToChart_transition R a h)).hom.app
        ((moduleToDerived R (FiniteOverlapVertexObject R a U)ᵒᵖ).obj X.as.obj) ≫
    (transitionDerivedRestrictionCompIso
      (diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h)
      (finiteOverlapAlgebraVertexToChart R a U)
      ((diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h).comp
        (finiteOverlapAlgebraVertexToChart R a U)) rfl).inv.app
        ((moduleToDerived R (FiniteOverlapVertexObject R a U)ᵒᵖ).obj X.as.obj) = _
  rw [transitionDerivedRestrictionCompIso_hom_app_Q,
    transitionDerivedRestrictionCompIso_inv_app_Q,
    finiteOverlapAlgebraRestrictionSquare_native_hom,
    finiteOverlapAlgebraRestrictionSquare_normal_inv,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  change 𝟙 ((finiteOverlapDerivedTransitionRestriction R a h ⋙
    finiteOverlapAlgebraDerivedRestriction R a T).obj X) ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _

end SerrePositivity.KST.DerivedBlowup
