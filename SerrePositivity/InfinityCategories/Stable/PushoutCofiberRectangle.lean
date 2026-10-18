module
public import SerrePositivity.InfinityCategories.Stable.ZeroEndPasting
public import SerrePositivity.InfinityCategories.Stable.CofiberRotationComparison
public import SerrePositivity.InfinityCategories.Stable.CofiberConnectingNaturality
public import SerrePositivity.InfinityCategories.Stable.CofiberTriangleNaturality

/-! # 押し出し四角形に沿う二つの cofiber

概要：任意の押し出し四角形の右下へ零対象を付加し、外側と右面の転置を cofiber 列とする。
方針：零終点の長方形を使い、外側から右面への比較を転置する。
規約：左面には零角を仮定しない。使われ方：八面体の最後の三角形と接続射の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定押し出しの右に零対象を付加した押し出し長方形。
方針：左面の一致、右下の零性、右面と外側の普遍性を保持する。
規約：左面の角の零性は不要。使われ方：押し出しに沿う二つの cofiber の同時構成。 -/
structure PushoutCofiberRectangle {X : SSet.{u}}
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) where
  diagram : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X
  left_eq : pastingSquare diagram 2 = L
  zero_end : IsZeroVertex (squareVertex (pastingSquare diagram 0) 1 0)
  right_isPushout : IsPushoutSquare (pastingSquare diagram 0)
  outer_isPushout : IsPushoutSquare (pastingSquare diagram 1)

/-- 概要：任意の押し出し四角形は零終点の長方形へ延長できる。
方針：右下の対象から選んだ零対象へ向かう辺を含む合成二単体を作る。
規約：左面を厳密に保持する。使われ方：八面体の第二の長方形の存在。 -/
lemma nonempty_pushoutCofiberRectangle {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : IsPushoutSquare L) :
    Nonempty (PushoutCofiberRectangle L) := by
  let z := chosenZeroVertex X
  obtain ⟨τ, hτ, hlast⟩ :=
    exists_terminalCompositeTriangle z.isTerminal (squareBottomArrow L)
  have h : squareBottomEdge ≫ L = stdSimplex.δ (2 : Fin 3) ≫ τ := by
    rw [hτ, squareBottomArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  have hz : IsZeroVertex (τ.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3))) := by
    rw [hlast]
    exact z.isZero
  obtain ⟨F, hleft, hbottom, hright, houter⟩ := exists_pushoutRectangle_of_zeroEnd L hL τ h hz
  refine ⟨⟨F, hleft, ?_, hright, houter⟩⟩
  change IsZeroVertex ((pastingBottomTriangle F).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))
  rw [hbottom]
  exact hz

/-- 概要：指定押し出しの cofiber 比較長方形を選ぶ。
方針：存在定理から選択する。
規約：左面の押し出し性を入力する。使われ方：八面体の具体的な代表。 -/
def chosenPushoutCofiberRectangle {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : IsPushoutSquare L) :
    PushoutCofiberRectangle L := Classical.choice (nonempty_pushoutCofiberRectangle L hL)

/-- 概要：長方形の外側の転置は零角の列。
方針：右下の零頂点を転置で標準の零角へ移す。
規約：始点と終点は外側の対角頂点。使われ方：押し出しの第一の cofiber 列。 -/
def PushoutCofiberRectangle.outerZeroTriangle {X : SSet.{u}}
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) : ZeroTriangle X where
  square := (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ pastingSquare r.diagram 1
  zero_corner := by
    change IsZeroVertex (squareVertex (pastingSquare r.diagram 0) 1 0)
    exact r.zero_end

/-- 概要：長方形の右面の転置は零角の列。
方針：右下の零頂点を転置で標準の零角へ移す。
規約：始点は中央下、終点は右上。使われ方：二つの cofiber の間の列。 -/
def PushoutCofiberRectangle.rightZeroTriangle {X : SSet.{u}}
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) : ZeroTriangle X where
  square := (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ pastingSquare r.diagram 0
  zero_corner := by
    change IsZeroVertex (squareVertex (pastingSquare r.diagram 0) 1 0)
    exact r.zero_end

/-- 概要：外側を転置した列は cofiber 列。
方針：押し出し性の転置不変性を使う。
規約：指定長方形の後は充填性不要。使われ方：八面体の二つ目の元の射の cofiber。 -/
lemma PushoutCofiberRectangle.outer_isCofiber {X : SSet.{u}}
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) :
    IsCofiberSequence r.outerZeroTriangle := (isPushoutSquare_iff_transpose _).1 r.outer_isPushout

/-- 概要：右面を転置した列は cofiber 列。
方針：押し出し性の転置不変性を使う。
規約：指定長方形の後は充填性不要。使われ方：八面体の最後の三角形の代表。 -/
lemma PushoutCofiberRectangle.right_isCofiber {X : SSet.{u}}
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) :
    IsCofiberSequence r.rightZeroTriangle := (isPushoutSquare_iff_transpose _).1 r.right_isPushout

/-- 概要：外側の cofiber 列から右面の cofiber 列への実際のホモトピー。
方針：外側から右面への形状の変形を転置で前合成する。
規約：時間の向きは外側から右面。使われ方：接続射の合成表示の比較。 -/
def PushoutCofiberRectangle.comparisonHomotopy {X : SSet.{u}}
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) :
    SSet.Homotopy r.outerZeroTriangle.square r.rightZeroTriangle.square :=
  stableHomotopyPrecomp (β_ (Δ[1] : SSet.{u}) Δ[1]).hom
    (pastingOuterToRightHomotopy r.diagram)

/-- 概要：二つの cofiber 列の比較ホモトピーを関手圏の h の射へ移す。
方針：比較を表す関手辺の類を取る。
規約：充填性は不要。使われ方：最後の三角形の接続射の合成表示。 -/
def PushoutCofiberRectangle.comparisonHom {X : SSet.{u}}
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) :
    (SSet.HomotopyCategory.mk (functorVertex r.outerZeroTriangle.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (functorVertex r.rightZeroTriangle.square) :=
  SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r.comparisonHomotopy)

/-- 概要：cofiber 比較の始点成分を列の始点間の射として表す。
方針：対角評価の射を、始点の頂点表示へ戻す。
規約：評価成分そのものを使う。使われ方：シフトの計算で端点の型を固定する。 -/
def PushoutCofiberRectangle.sourceHom {X : SSet.{u}} [Quasicategory X]
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) :
    squareHoVertex r.outerZeroTriangle.square 0 0 ⟶
      squareHoVertex r.rightZeroTriangle.square 0 0 :=
  (squareDiagramHoEvaluation X 0 0).map r.comparisonHom

/-- 概要：cofiber 比較の始点成分は左面の下辺である。
方針：転置で対角成分を保ち、元の比較の始点の計算を使う。
規約：端点は Arrow の等号で照合する。使われ方：懸垂に送る元の射の同定。 -/
lemma PushoutCofiberRectangle.comparisonHom_source_arrow {X : SSet.{u}} [Quasicategory X]
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) :
    Arrow.mk r.sourceHom =
      Arrow.mk (squareHoBottom L) := by
  change Arrow.mk ((squareDiagramHoEvaluation X 0 0).map
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (stableHomotopyPrecomp (β_ (Δ[1] : SSet.{u}) Δ[1]).hom
        (pastingOuterToRightHomotopy r.diagram))))) = _
  rw [← homMk_functorEdge_precomp]
  rw [squareDiagramHoEvaluation_transpose]
  exact (pastingOuterToRightHom_source_arrow r.diagram).trans (congrArg
    (fun R => Arrow.mk (squareHoBottom R)) r.left_eq)

/-- 概要：cofiber 比較の終点成分は恒等射である。
方針：転置で対角成分を保ち、固定した終点の計算を使う。
規約：二つの列の終点は同じ頂点。使われ方：接続射の自然性から恒等成分を消す。 -/
lemma PushoutCofiberRectangle.comparisonHom_target {X : SSet.{u}} [Quasicategory X]
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) :
    (squareDiagramHoEvaluation X 1 1).map r.comparisonHom =
      𝟙 (squareHoVertex r.outerZeroTriangle.square 1 1) := by
  change (squareDiagramHoEvaluation X 1 1).map
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (stableHomotopyPrecomp (β_ (Δ[1] : SSet.{u}) Δ[1]).hom
        (pastingOuterToRightHomotopy r.diagram)))) = _
  rw [← homMk_functorEdge_precomp]
  rw [squareDiagramHoEvaluation_transpose]
  exact pastingOuterToRightHom_target r.diagram

/-- 概要：右面の cofiber 接続射は外側の接続射と左面の下辺の懸垂との合成。
方針：実際の比較に接続射の自然性を適用し、終点の恒等成分を消す。
規約：下辺は始点成分として端点を輸送している。使われ方：八面体の最後の第三射。 -/
lemma PushoutCofiberRectangle.connecting_comp {X : SSet.{u}} [Quasicategory X] [IsStable X]
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) :
    cofiberConnecting r.rightZeroTriangle r.right_isCofiber =
      cofiberConnecting r.outerZeroTriangle r.outer_isCofiber ≫
        (suspensionFunctor X).map r.sourceHom := by
  have h := cofiberConnecting_naturality r.outerZeroTriangle r.rightZeroTriangle
    r.outer_isCofiber r.right_isCofiber r.comparisonHom
  erw [r.comparisonHom_target, Category.id_comp] at h
  exact h

set_option maxHeartbeats 1000000 in
-- 具体的な転置図式のシフトを照合するカーネル検査が既定の計算上限を超えるため。
/-- 概要：右面の cofiber 三角形の第三射は外側の第三射と始点成分の一回シフトの合成。
方針：懸垂に値を取る合成式を一回シフトとの比較の自然性で移す。
規約：負号を追加しない通常の第三射。使われ方：八面体の最後の三角形の所属。 -/
lemma PushoutCofiberRectangle.triangle_connecting_comp {X : SSet.{u}}
    [Quasicategory X] [IsStable X]
    {L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (r : PushoutCofiberRectangle L) :
    (cofiberTriangle r.rightZeroTriangle r.right_isCofiber).mor₃ =
      (cofiberTriangle r.outerZeroTriangle r.outer_isCofiber).mor₃ ≫
        (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map r.sourceHom := by
  have h := cofiberTriangle_mor₃_naturality r.outerZeroTriangle r.rightZeroTriangle
    r.outer_isCofiber r.right_isCofiber
    r.sourceHom
    (𝟙 r.outerZeroTriangle.hoShortComplex.X₃)
    ((Category.id_comp _).trans r.connecting_comp)
  exact (Category.id_comp _).symm.trans h

end SerrePositivity.InfinityCategories
