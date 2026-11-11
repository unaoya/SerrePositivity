module
public import SerrePositivity.KST.SConstruction.CofiberUnitComparison

/-! # 固定 span に沿う三つの比較 prism
概要：単位の中間正方形を元の cofiber 正方形へ比較する三つのホモトピーの形状。
方針：内部の横座標、区間の第二端点、区間の第一端点を max で順に動かす。
規約：このファイルでは形状だけを扱う。
使われ方：BGT Lemma 7.3 の固定 span を用いる押し出し性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：横座標を時刻との max に動かす。
方針：max の単体集合の射を第一座標に適用する。
規約：時刻は第一因子。使われ方：水平の比較 prism。 -/
def squareHorizontalPrism : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ Δ[1] ⊗ Δ[1] :=
  lift (lift (fst _ _) (snd _ _ ≫ fst _ _) ≫ intervalMax) (snd _ _ ≫ snd _ _)

/-- 概要：縦座標を時刻との max に動かす。
方針：max の単体集合の射を第二座標に適用する。
規約：時刻は第一因子。使われ方：区間の第一端点の比較 prism。 -/
def squareVerticalPrism : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ Δ[1] ⊗ Δ[1] :=
  lift (snd _ _ ≫ fst _ _) (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ intervalMax)

/-- 概要：縦座標を一に固定する。
方針：横座標を保ち第二座標を終点にする。
規約：正方形の自己写像。使われ方：縦 prism の終点。 -/
def cofiberTopCorner : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[1] :=
  lift (fst _ _) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))

/-- 概要：水平 prism の始点は恒等射。
方針：各単体の頂点で max 0 x = x を計算する。
規約：厳密等号。使われ方：比較の始点。 -/
lemma squareHorizontalPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ squareHorizontalPrism = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext r
    change max 0 (stdSimplex.asOrderHom s.1 r) = stdSimplex.asOrderHom s.1 r
    exact max_eq_right (Fin.zero_le _)
  · rfl

/-- 概要：水平 prism の終点は横座標一の単位。
方針：各単体の頂点で max 1 x = 1 を計算する。
規約：厳密等号。使われ方：比較の終点。 -/
lemma squareHorizontalPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ squareHorizontalPrism = cofiberUnitCorner := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext r
    change max 1 (stdSimplex.asOrderHom s.1 r) = 1
    exact max_eq_left (Fin.le_last _)
  · rfl

/-- 概要：縦 prism の始点は恒等射。
方針：各単体の頂点で max 0 y = y を計算する。
規約：厳密等号。使われ方：比較の始点。 -/
lemma squareVerticalPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ squareVerticalPrism = 𝟙 _ := by
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

/-- 概要：縦 prism の終点は縦座標一。
方針：各単体の頂点で max 1 y = 1 を計算する。
規約：厳密等号。使われ方：比較の終点。 -/
lemma squareVerticalPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ squareVerticalPrism = cofiberTopCorner := by
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

/-- 概要：第一端点を i に固定した区間の族。
方針：横は i→j、縦は定値 i とする。
規約：x=0 は対角 (i,i)。使われ方：三つの比較の共通パラメーター。 -/
def arFixedStartSquare {n : ℕ} (a : Ar.{u} n) : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n :=
  arSquare a.down.val.1 a.down.val.1 a.down.val.1 a.down.val.2 le_rfl le_rfl a.down.property

/-- 概要：区間 (i,k) と内部座標 (x,y) を取る比較の正方形 T。
方針：第一端点を固定した形状と恒等座標を合わせる。
規約：押し出し性は含めない。使われ方：元の cofiber と単位の中間の比較。 -/
def arCofiberComparisonSquare {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1]) :=
  lift (arFixedStartSquare a) (𝟙 _)

/-- 概要：区間 (i,k) と内部座標 (1,y) を取る比較の正方形 U。
方針：第一端点を固定した形状と単位の座標を合わせる。
規約：押し出し性は含めない。使われ方：二つの単位比較の共通終点。 -/
def arCofiberComparisonUnitSquare {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1]) :=
  lift (arFixedStartSquare a) cofiberUnitCorner

/-- 概要：内部の横座標だけを動かす T→U の prism。
方針：パラメーターを保って水平 prism を適用する。
規約：x=0 のパラメーターは対角。使われ方：対角の枠による恒等性。 -/
def arCofiberHorizontalPrism {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1]) :=
  lift (snd _ _ ≫ arFixedStartSquare a) squareHorizontalPrism

/-- 概要：区間の第二端点を動かす T→H(a) の prism。
方針：内部座標を保ってパラメーターに水平 prism を適用する。
規約：x=0 の二つの角は固定 span の左辺。使われ方：入力の第二端点独立性。 -/
def arCofiberTargetPrism {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1]) :=
  lift (squareHorizontalPrism ≫ arFixedStartSquare a) (snd _ _)

/-- 概要：区間の第一端点を動かす D→U の prism。
方針：単位の座標を保って標準正方形のパラメーターに縦 prism を適用する。
規約：y=0 の角は固定 span の下辺の終点。使われ方：入力の第一端点独立性。 -/
def arCofiberSourcePrism {n : ℕ} (a : Ar.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n ⊗ (Δ[1] ⊗ Δ[1]) :=
  lift (squareVerticalPrism ≫ arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2
    (Fin.zero_le _) le_rfl a.down.property) (snd _ _ ≫ cofiberUnitCorner)

/-- 概要：第一端点を固定した形状の右辺は元の区間で定値。
方針：横座標一と、等しい二つの第一端点を計算する。
規約：全次数の等号。使われ方：T→H(a) の終点。 -/
lemma arFixedStartSquare_unitCorner {n : ℕ} (a : Ar.{u} n) :
    cofiberUnitCorner ≫ arFixedStartSquare a = SSet.const (ComposableArrows.mk₀ a) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change (if _ = 0 then a.down.val.1 else a.down.val.1) = _
    simp only [ite_self] <;> rfl
  · rfl

/-- 概要：標準正方形の上辺は第一端点を固定した形状。
方針：縦座標一で標準正方形を評価する。
規約：全次数の等号。使われ方：D→U の終点。 -/
lemma arSquare_topCorner {n : ℕ} (a : Ar.{u} n) :
    cofiberTopCorner ≫ arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2
      (Fin.zero_le _) le_rfl a.down.property = arFixedStartSquare a := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change a.down.val.1 = (if _ = 0 then a.down.val.1 else a.down.val.1)
    simp only [ite_self] <;> rfl
  · rfl

/-- 概要：内部横座標の比較は T から始まる。
方針：水平 prism の始点を使う。規約：厳密等号。使われ方：比較同型の始域。 -/
lemma arCofiberHorizontalPrism_zero {n : ℕ} (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberHorizontalPrism a =
      arCofiberComparisonSquare a := by
  rw [arCofiberHorizontalPrism, comp_lift, squareHorizontalPrism_zero]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, ← Category.assoc, lift_snd, Category.id_comp]
  rfl

/-- 概要：内部横座標の比較は U に終わる。
方針：水平 prism の終点を使う。規約：厳密等号。使われ方：比較同型の終域。 -/
lemma arCofiberHorizontalPrism_one {n : ℕ} (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberHorizontalPrism a =
      arCofiberComparisonUnitSquare a := by
  rw [arCofiberHorizontalPrism, comp_lift, squareHorizontalPrism_one]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, ← Category.assoc, lift_snd, Category.id_comp]
  rfl

/-- 概要：区間の第二端点の比較は T から始まる。
方針：水平 prism の始点を使う。規約：厳密等号。使われ方：比較同型の始域。 -/
lemma arCofiberTargetPrism_zero {n : ℕ} (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberTargetPrism a =
      arCofiberComparisonSquare a := by
  rw [arCofiberTargetPrism, comp_lift, ← Category.assoc, squareHorizontalPrism_zero]
  simp only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_snd]
  rfl

/-- 概要：区間の第二端点の比較は元の区間の四角形に終わる。
方針：水平 prism の終点と右辺での定値性を使う。
規約：厳密等号。使われ方：選んだ H(a) との比較。 -/
lemma arCofiberTargetPrism_one {n : ℕ} (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberTargetPrism a =
      lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 _) := by
  rw [arCofiberTargetPrism, comp_lift, ← Category.assoc, squareHorizontalPrism_one,
    arFixedStartSquare_unitCorner]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_snd]

/-- 概要：区間の第一端点の比較は単位の中間正方形 D から始まる。
方針：縦 prism の始点を使う。規約：厳密等号。使われ方：比較同型の始域。 -/
lemma arCofiberSourcePrism_zero {n : ℕ} (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberSourcePrism a =
      arCofiberUnitSquare a := by
  rw [arCofiberSourcePrism, comp_lift, ← Category.assoc, squareVerticalPrism_zero]
  simp only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, ← Category.assoc, lift_snd]
  rfl

/-- 概要：区間の第一端点の比較は U に終わる。
方針：縦 prism の終点と標準正方形の上辺の形状を使う。
規約：厳密等号。使われ方：比較同型の終域。 -/
lemma arCofiberSourcePrism_one {n : ℕ} (a : Ar.{u} n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] ⊗ Δ[1] : SSet.{u}) ≫ arCofiberSourcePrism a =
      arCofiberComparisonUnitSquare a := by
  rw [arCofiberSourcePrism, comp_lift, ← Category.assoc, squareVerticalPrism_one, arSquare_topCorner]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, ← Category.assoc, lift_snd, Category.id_comp]
  rfl

end SerrePositivity.KST.SConstruction
