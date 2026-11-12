module
public import SerrePositivity.KST.SConstruction.FramePreservingSpanCompletion
public import SerrePositivity.KST.SConstruction.GappedOriginSquares
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso

/-! # cofiber の単位と標準抽出を比較する prism
概要：各区間の標準四角形に沿う cofiber の単位を右上角へ動かす。
方針：区間座標の max を用いて実際の単体的ホモトピーを構成する。
規約：枠上の正方形の厳密な指定を利用する。
使われ方：BGT Lemma 7.3 の補完後の図式の普遍性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：二つの標準区間の座標の最大値を取る順序写像。
方針：max の両変数での単調性を使う。
規約：ULift による universe の一致。使われ方：単位比較の prism。 -/
def intervalMaxOrder : ULift.{u} (Fin 2 × Fin 2) →o ULift.{u} (Fin 2) where
  toFun p := ULift.up (max p.down.1 p.down.2)
  monotone' _ _ h := max_le_max h.1 h.2

/-- 概要：標準区間の二座標の max を取る単体集合の射。
方針：標準単体の nerve 表示で順序写像を送る。
規約：左右の端点も含む。使われ方：prism の縦座標。 -/
def intervalMax : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] :=
  (prodStdSimplex.isoNerve 1 1).hom ≫ nerveMap intervalMaxOrder.toFunctor ≫
    (stdSimplex.isoNerve 1).inv

/-- 概要：時刻零で max は第二座標に等しい。
方針：鎖の頂点で有限区間の最小元を計算する。
規約：厳密等号。使われ方：prism の始点。 -/
lemma intervalMax_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ intervalMax = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext r
  change max 0 (stdSimplex.asOrderHom s r) = stdSimplex.asOrderHom s r
  exact max_eq_right (Fin.zero_le _)

/-- 概要：時刻一で max は一に等しい。
方針：鎖の頂点で有限区間の最大元を計算する。
規約：厳密等号。使われ方：prism の終点。 -/
lemma intervalMax_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ intervalMax =
    SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext r
  change max 1 (stdSimplex.asOrderHom s r) = 1
  exact max_eq_left (Fin.le_last _)

/-- 概要：標準正方形の横座標を一、縦座標を時刻との max に置く。
方針：座標射影と max の単体集合の射を組み合わせる。
規約：時刻は第一因子。使われ方：cofiber の単位から右上角への移動。 -/
def cofiberUnitCornerPrism : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ Δ[1] ⊗ Δ[1] :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ intervalMax)

/-- 概要：標準正方形に沿う区間と、単位を右上角へ動かす座標を合わせる。
方針：区間の添字は固定し、内部正方形の縦座標だけを動かす。
規約：a は一つの区間。使われ方：標準 cofiber 抽出への比較。 -/
def arCofiberUnitPrism {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1]) :=
  lift (snd _ _ ≫ arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2
    (Fin.zero_le _) le_rfl a.down.property) cofiberUnitCornerPrism

/-- 概要：prism の始点で横座標一の単位正方形を取る。
方針：横座標を一に固定し、縦座標は保つ。
規約：元の正方形と同じ値域。使われ方：比較の中間正方形。 -/
def cofiberUnitCorner : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[1] :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (snd _ _)

/-- 概要：単位の prism は時刻零で元の単位に等しい。
方針：鎖の頂点で max 0 y = y を使う。
規約：厳密等号。使われ方：ホモトピーの始点。 -/
lemma cofiberUnitCornerPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ cofiberUnitCornerPrism = cofiberUnitCorner := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext r
    change max 0 (stdSimplex.asOrderHom s.2 r) = stdSimplex.asOrderHom s.2 r
    exact max_eq_right (Fin.zero_le _)

/-- 概要：単位の prism は時刻一で右上角に定値。
方針：鎖の頂点で max 1 y = 1 を使う。
規約：厳密等号。使われ方：ホモトピーの終点。 -/
lemma cofiberUnitCornerPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ cofiberUnitCornerPrism =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext r
    change max 1 (stdSimplex.asOrderHom s.2 r) = 1
    exact max_eq_left (Fin.le_last _)

/-- 概要：標準正方形の各区間で cofiber の右辺を取る中間正方形。
方針：標準四角形の添字と横座標一の単位を組み合わせる。
規約：四角形の普遍性を含まない形状。使われ方：標準抽出への関手同型の始域。 -/
def arCofiberUnitSquare {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1]) :=
  lift (arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2
    (Fin.zero_le _) le_rfl a.down.property) cofiberUnitCorner

/-- 概要：単位 prism の始点は単位の中間正方形。
方針：prism の始点と積の座標を計算する。
規約：全次数の厳密等号。使われ方：単位比較の始点の同定。 -/
lemma arCofiberUnitPrism_zero {n : ℕ} (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberUnitPrism a =
      arCofiberUnitSquare a := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply ULift.ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext r
      change max 0 (stdSimplex.asOrderHom s.2 r) = stdSimplex.asOrderHom s.2 r
      exact max_eq_right (Fin.zero_le _)

/-- 概要：単位 prism の終点は標準正方形の後で各区間の右上角を取る形状。
方針：prism の終点と積の座標を計算する。
規約：全次数の厳密等号。使われ方：右上角の図式の標準抽出。 -/
lemma arCofiberUnitPrism_one {n : ℕ} (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberUnitPrism a =
      arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property ≫
        lift (𝟙 (arNerve n)) (SSet.const
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply ULift.ext
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext r
      change max 1 (stdSimplex.asOrderHom s.2 r) = 1
      exact max_eq_left (Fin.le_last _)

end SerrePositivity.KST.SConstruction
