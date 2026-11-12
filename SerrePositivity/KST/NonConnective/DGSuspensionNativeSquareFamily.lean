module
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeActionInput
public import SerrePositivity.KST.NonConnective.DGKappaResolvedConnectiveSquare

/-!
概要：採用済みの同じ全四角形族を受け、全 native 入力上の関手空間の族として使う。
方針：同じ全族を curry し、元の全四角形・包含・商辺を厳密に回収する。
規約：全族と元の実四角形への一致に条件付き。全族や Morita・P 自然比較の存在は主張しない。
使われ方：K-7 c4・c5 の D-8 e 供給仕様の利用側。供給境界の完成とは数えない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R]
  (F : ((Δ[1] ⊗ Δ[1]) ⊗ dgKInputInfinity.{u, max (u + 1) v} R) ⟶
    dgKInputInfinity.{u, max (u + 1) v} R)

/-- 概要：同じ全四角形族を全 native 入力上の関手空間の族へ移す。
方針：四角形を固定する内部 Hom へ同じ全族を curry する。
規約：全族の選択や構成は行わない。
使われ方：四角形の全二胞体と全 native 入力の作用を同時に保持する。 -/
def dgSuspensionNativeSquareDiagramFamily : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    (ihom (Δ[1] ⊗ Δ[1])).obj (dgKInputInfinity.{u, max (u + 1) v} R) :=
  curry F

/-- 概要：関手空間表示から元の全四角形族を厳密に回収する。
方針：curry の逆を使う。
規約：頂点やホモトピー類だけの回収に弱めない。
使われ方：D が供給する同じ全高次族との照合。 -/
theorem dgSuspensionNativeSquareDiagramFamily_recovery :
    uncurry (dgSuspensionNativeSquareDiagramFamily R F) = F :=
  uncurry_curry F

/-- 概要：同じ全族を元の入力 A に制限した全四角形。
方針：関手空間の元の頂点を実四角形へ戻す。
規約：各入力で別の四角形を選び直さない。
使われ方：採用済みの元の実核・cone・零角・懸垂との厳密一致条件。 -/
def dgSuspensionNativeSquareAt (A : PerfDGInput.{u, max (u + 1) v} R) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((dgSuspensionNativeSquareDiagramFamily R F).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A))

/-- 概要：同じ全族の任意の指定一辺を全 native 入力上の族として取り出す。
方針：元の四角形の辺による前合成を行う。
規約：辺の族は全単体を持つ同じ実射である。
使われ方：包含・商・零角の元の一単体との照合。 -/
def dgSuspensionNativeSquareFaceFamily (e : (Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
    Δ[1] ⊗ Δ[1]) : dgKInputInfinity.{u, max (u + 1) v} R ⟶
      (ihom Δ[1]).obj (dgKInputInfinity.{u, max (u + 1) v} R) :=
  dgSuspensionNativeSquareDiagramFamily R F ≫ (pre e).app _

/-- 概要：同じ全四角形族の各角を全 native 入力上の実作用として取り出す。
方針：指定角での評価関手を後合成する。
規約：頂点ごとの任意選択で作用を代用しない。
使われ方：実核・cone・零角・懸垂を持つ同じ全族の入力作用。 -/
def dgSuspensionNativeSquareCornerFamily (i j : Fin 2) :
    dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R :=
  dgSuspensionNativeSquareDiagramFamily R F ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

/-- 概要：同じ全四角形族を元の固定 K で全 native 入力に同時に作用させる。
方針：関手空間の固定 K による後合成を使う。
規約：固定 dgKInputInfinity・ν・K を変更しない。
使われ方：元の全四角形族から構造射の全入力自然性への利用側。 -/
def dgSuspensionNativeKSquareFamily : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    (ihom (Δ[1] ⊗ Δ[1])).obj Sp.{max (u + 1) v} :=
  dgSuspensionNativeSquareDiagramFamily R F ≫ (ihom (Δ[1] ⊗ Δ[1])).map (dgKInputK R)

/-- 概要：固定 K の全四角形族は元の同じ全族の K 像を厳密に回収する。
方針：後合成に対する uncurry の自然性と全族の回収を使う。
規約：各入力の四辺だけの照合に弱めない。
使われ方：全 native Hom を保つ同じ K 四角形族の比較。 -/
theorem dgSuspensionNativeKSquareFamily_recovery :
    uncurry (dgSuspensionNativeKSquareFamily R F) = F ≫ dgKInputK R := by
  rw [dgSuspensionNativeKSquareFamily, uncurry_natural_right,
    dgSuspensionNativeSquareDiagramFamily_recovery]

variable {κ : Cardinal.{u}} (s : DGSuspensionStageProvider.{u, v} R κ)
  (hF : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    dgSuspensionNativeSquareAt R F A = dgKappaResolvedConnectiveSquare R A (s A).cone)

include hF in
/-- 概要：採用済みの全四角形一致に条件付きで、各辺族は元の同じ実辺を回収する。
方針：全四角形の頂点表示と元の辺による前合成を照合する。
規約：全四角形一致の供給の存在は主張しない。
使われ方：元の実核包含・商射影を全 native 族の値として保持する。 -/
theorem dgSuspensionNativeSquareFaceFamily_at
    (e : (Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ Δ[1] ⊗ Δ[1])
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgSuspensionNativeSquareFaceFamily R F e).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (e ≫ dgKappaResolvedConnectiveSquare R A (s A).cone) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgSuspensionNativeSquareAt R F A) =
      (dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change ((pre e).app _).app (Opposite.op ⦋0⦌)
    ((dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [← hv, hF A]
  rfl

include hF in
/-- 概要：全族一致に条件付きで、各角の全 native 作用は元の実角を回収する。
方針：同じ全四角形の回収を評価関手へ送る。
規約：角の対象一致から全 native 作用の一意性は推論しない。
使われ方：D-8 e の実核・cone・零角・懸垂の作用を照合する。 -/
theorem dgSuspensionNativeSquareCornerFamily_at (i j : Fin 2)
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgSuspensionNativeSquareCornerFamily R F i j).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgKappaResolvedConnectiveSquare R A (s A).cone) i j := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgSuspensionNativeSquareAt R F A) =
      (dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)).app (Opposite.op ⦋0⦌)
    ((dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [← hv, hF A, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  rfl

include hF in
/-- 概要：全族一致に条件付きで、固定 K の各値は元の実四角形全体の K 像。
方針：同じ全四角形の頂点を回収して固定 K を後合成する。
規約：Sp の引き戻し性や全入力 Morita 比較は結論しない。
使われ方：K-7 c4・c5 の元の実核・cone・零角・懸垂の固定 K 像。 -/
theorem dgSuspensionNativeKSquareFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgSuspensionNativeKSquareFamily R F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgKappaResolvedConnectiveSquare R A (s A).cone ≫ dgKInputK R) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgSuspensionNativeSquareAt R F A) =
      (dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change ((ihom (Δ[1] ⊗ Δ[1])).map (dgKInputK R)).app (Opposite.op ⦋0⦌)
    ((dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [← hv, hF A]
  rfl

include hF in
/-- 概要：同じ全族の下辺は元の実核包含の全一単体を回収する。
方針：全四角形一致と元の固定零化四角形の指定下辺を使う。
規約：I・P とは別の全族供給に条件付き。
使われ方：D-8 e の全入力自然性と同じ実包含の照合。 -/
theorem dgSuspensionNativeSquareBottomFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgSuspensionNativeSquareFaceFamily R F _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaResolvedKernelInputMap R A (s A).cone)).edge) := by
  rw [dgSuspensionNativeSquareFaceFamily_at R F s hF]
  rw [(dgKappaResolvedConnectiveSquare_edges R A (s A).cone).1]

include hF in
/-- 概要：同じ全族の右辺は元の実商射影の全一単体を回収する。
方針：全四角形一致と元の固定零化四角形の指定右辺を使う。
規約：Morita・P 自然比較をこの回収だけから結論しない。
使われ方：D-8 e の全入力自然性と同じ実商射影の照合。 -/
theorem dgSuspensionNativeSquareRightFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgSuspensionNativeSquareFaceFamily R F _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaResolvedSuspensionInputMap R A (s A).cone)).edge) := by
  rw [dgSuspensionNativeSquareFaceFamily_at R F s hF]
  rw [(dgKappaResolvedConnectiveSquare_edges R A (s A).cone).2.1]

/-- 概要：供給された同じ全高次懸垂作用で、元の全四角形族の入力を反復する。
方針：元の全族へ同じ反復作用を前合成する。
規約：全族と全高次作用の供給に条件付き。各段の四角形は選び直さない。
使われ方：K-7 c4・c5 の全 native 入力上の反復四角形族。 -/
def dgSuspensionNativeSquareIterationFamily (a : DGSuspensionNativeActionInput R s) (n : ℕ) :=
  DGSuspensionNativeActionInput.iteration R s a n ≫ dgSuspensionNativeSquareDiagramFamily R F

/-- 概要：反復後も元の全四角形族を同じ入力作用で厳密に回収する。
方針：uncurry の前合成自然性を使う。
規約：全高次の単体を保ち、頂点別の比較に弱めない。
使われ方：同じ全族の全段での自然性と整合性。 -/
theorem dgSuspensionNativeSquareIterationFamily_recovery
    (a : DGSuspensionNativeActionInput R s) (n : ℕ) :
    uncurry (dgSuspensionNativeSquareIterationFamily R F s a n) =
      (Δ[1] ⊗ Δ[1]) ◁ DGSuspensionNativeActionInput.iteration R s a n ≫ F := by
  rw [dgSuspensionNativeSquareIterationFamily, uncurry_natural_left,
    dgSuspensionNativeSquareDiagramFamily_recovery]

/-- 概要：固定 K の全族も全 native 入力の各反復段で元の全高次族を回収する。
方針：入力の前合成自然性と固定 K の全族の回収を合成する。
規約：各段の点別比較だけに弱めない。
使われ方：同じ反復四角形の固定 K 像の全入力自然性。 -/
theorem dgSuspensionNativeKSquareIterationFamily_recovery
    (a : DGSuspensionNativeActionInput R s) (n : ℕ) :
    uncurry (DGSuspensionNativeActionInput.iteration R s a n ≫
        dgSuspensionNativeKSquareFamily R F) =
      ((Δ[1] ⊗ Δ[1]) ◁ DGSuspensionNativeActionInput.iteration R s a n ≫ F) ≫
        dgKInputK R := by
  rw [uncurry_natural_left, dgSuspensionNativeKSquareFamily_recovery, Category.assoc]

include hF in
/-- 概要：全族一致に条件付きで、各反復段は元の同じ実核・cone・零角・懸垂の全四角形。
方針：既存の全高次反復の頂点回収を同じ全族へ代入する。
規約：各段の二胞体を境界だけの一致で代用しない。
使われ方：K-7 c4・c5 の同じ対象別反復列への全族の制限。 -/
theorem dgSuspensionNativeSquareIterationFamily_at
    (a : DGSuspensionNativeActionInput R s)
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    (dgSuspensionNativeSquareIterationFamily R F s a n).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgKappaResolvedConnectiveSquare R
          (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone) := by
  change (dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
    ((DGSuspensionNativeActionInput.iteration R s a n).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [DGSuspensionNativeActionInput.iteration_vertex]
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgSuspensionNativeSquareAt R F (dgSuspensionIteration R s A n)) =
      (dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionIteration R s A n)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  rw [← hv, hF]
  rfl

include hF in
/-- 概要：反復全族の固定 K 像は、同じ元の各段の実 K 四角形を回収する。
方針：元の全高次反復の頂点と固定 K の全族の回収を合成する。
規約：全族・作用・実四角形一致に条件付き。Morita 自然比較の存在は主張しない。
使われ方：K-7 c5 の同じ実構造四角形の全入力・全段での利用側。 -/
theorem dgSuspensionNativeKSquareIterationFamily_at
    (a : DGSuspensionNativeActionInput R s)
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    (DGSuspensionNativeActionInput.iteration R s a n ≫
        dgSuspensionNativeKSquareFamily R F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgKappaResolvedConnectiveSquare R (dgSuspensionIteration R s A n)
        (dgSuspensionIterationStage R s A n).cone ≫ dgKInputK R) := by
  change (dgSuspensionNativeKSquareFamily R F).app (Opposite.op ⦋0⦌)
    ((DGSuspensionNativeActionInput.iteration R s a n).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [DGSuspensionNativeActionInput.iteration_vertex]
  exact dgSuspensionNativeKSquareFamily_at R F s hF (dgSuspensionIteration R s A n)

include hF in
/-- 概要：同じ全四角形族の懸垂角を既存の全高次懸垂作用の入力へ渡す。
方針：同じ族の (1,1) 角を map に固定し、頂点を元の実平坦懸垂へ回収する。
規約：全族一致・元の厳密 dg 射のデータ・辺照合に条件付き。供給の存在は主張しない。
使われ方：D-8 e の全四角形供給から既存の条件付き全高次反復への接続。 -/
def DGSuspensionNativeActionInput.ofSquareFamily
    (d : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R}, (A ⟶ B) →
      DGKappaSuspensionMapData R A B (s A).cone (s B).cone)
    (hedge : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B),
      (dgSuspensionNativeSquareCornerFamily R F 1 1).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (d f))).edge) :
    DGSuspensionNativeActionInput R s where
  map := dgSuspensionNativeSquareCornerFamily R F 1 1
  vertex A := (dgSuspensionNativeSquareCornerFamily_at R F s hF 1 1 A).trans
    (dgKappaResolvedConnectiveSquare_vertices R A (s A).cone).2.2.1
  data := d
  edge := hedge

end SerrePositivity.KST.NonConnective
