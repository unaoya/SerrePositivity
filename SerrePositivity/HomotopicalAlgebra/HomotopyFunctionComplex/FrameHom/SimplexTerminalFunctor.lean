module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.SimplexTerminalAugmentation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveMonos
public import SerrePositivity.KST.ProExcision.NerveOppositeIso

/-!
# 反対要素圏の nerve の関手と余連続性

概要：終端 augmentation の始域を同じ全単体の関手へ束ねる。
方針：既存の反対 nerve の自然な同型で通常の要素圏の nerve の反転と比較する。
規約：三本矢の共通比較と同じ反対要素圏を保持する。
使われ方：任意の単体集合での augmentation の反転性の cellular な証明。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- 概要：反対要素圏の同じ nerve は単体集合に関して関手をなす（Dwyer–Kan §7）。
方針：元の係数写像を要素圏・反対圏・nerve に送る。
規約：全単体と全作用素を保持する。
使われ方：同じ終端 augmentation の始域。 -/
def functor : SSet.{v} ⥤ SSet.{v} where
  obj K := nerve K.Elementsᵒᵖ
  map f := nerveMap f.mapElements.op

/-- 概要：反対要素圏の nerve は元の要素圏の nerve の反転と自然に同型（Dwyer–Kan）。
方針：既存の同じ射列の反転の実同型を要素圏へ適用する。
規約：圏の反対と単体集合の反転を同一視しない。
使われ方：余極限と単射の保存の移送。 -/
def oppositeIso : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor.{v} ≅ SerrePositivity.SimplicialModel.SimplexNerve.functor ⋙
    SSet.opFunctor :=
  NatIso.ofComponents (fun K => SerrePositivity.KST.ProExcision.nerveOppositeIso K.Elements)
    (fun f => SerrePositivity.KST.ProExcision.nerveOppositeIso_natural _ f.mapElements)

/-- 概要：反対要素圏の同じ nerve は小余極限を保つ（Dwyer–Kan §7）。
方針：元の要素圏の nerve の余連続性と単体集合の反転同値を使う。
規約：局所化関手の余連続性は要求しない。
使われ方：cellular な帰納の実際の始域関手。 -/
instance preservesColimits : PreservesColimitsOfSize.{v, v} _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor.{v} := by
  let : SSet.opFunctor.{v}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  exact (preservesColimitsOfSize_iff_of_natIso _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.oppositeIso).mpr inferInstance

/-- 概要：反対要素圏の同じ nerve は単射を保つ（Dwyer–Kan §7）。
方針：元の要素圏の単射保存と単体集合の反転同値から移す。
規約：元の比較関手を別の関手へ置き換えない。
使われ方：境界の貼り合わせに沿う反転性の帰納。 -/
instance preservesMonomorphisms : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor.{v}.PreservesMonomorphisms := by
  let : SSet.opFunctor.{v}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  exact CategoryTheory.Functor.PreservesMonomorphisms.of_iso _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.oppositeIso.symm

/-- 概要：同じ終端 augmentation は全単体集合に自然な比較（Dwyer–Kan §7）。
方針：元の全係数自然性を同じ関手に束ねる。
規約：各成分は元の終端単体の制限そのもの。
使われ方：cellular な比較の反転性。 -/
def augmentation : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor.{v} ⟶ 𝟭 _ where
  app K := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalAugmentation.augmentation K
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalAugmentation.naturality _ f

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve
