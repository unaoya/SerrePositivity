module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic


/-!
# 通常の可換代数圏と perfectoid 標的の充満部分圏

nerve・指定錐と独立な通常の圏、商図式、付値環への一意延長条件。
-/

universe u

/-! ## Perfectoid 化界面の通常の添字圏

概要：同じ宇宙の可換代数、導来 p 完備な代数、perfectoid 標的の圏を定める。
方針：可換環の under 圏と充満部分圏を用いる。
規約：台環は Type u、圏の対象は Type (u+1)。巨大極限の存在は要求しない。
使われ方：E3 界面の始域と BS 著者版 Proposition 8.5 の制限した添字圏。
-/

@[expose] public section Setup

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.CategoryTheory
open _root_.SerrePositivity.DerivedCompletion

/-- Type u の通常の可換 R 代数の圏。構造射をデータとして保持する。 -/
abbrev A_R (R : Type u) [CommRing R] := Under (CommRingCat.of R)

/-- 通常の R 代数を、元の代数構造の射とともに束ねる。 -/
def ofAlgebra (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : A_R R :=
  Under.mk (CommRingCat.ofHom (algebraMap R S))

/-- 始域に課す導来 p 完備性。通常の p 進完備性へ置き換えない。 -/
def completeProperty (R : Type u) [CommRing R] (p : ℕ) : ObjectProperty (A_R R) :=
  fun S => IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right)

/-- 導来 p 完備な通常の R 代数の充満部分圏。 -/
abbrev C_R (R : Type u) [CommRing R] (p : ℕ) := (completeProperty R p).FullSubcategory

/-- 完備性の条件だけを忘れる包含関手。 -/
abbrev completeInclusion (R : Type u) [CommRing R] (p : ℕ) : C_R R p ⥤ A_R R :=
  (completeProperty R p).ι

/-- S の下の環のうち、標的が perfectoid であるという性質。 -/
def perfectoidTargetProperty (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :
    ObjectProperty (Under S) := fun T => IsIntegralPerfectoid T.right p

/-- Type u の perfectoid 標的 S → T の圏。射の向きを反転しない。 -/
abbrev PerfUnder_u (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :=
  (perfectoidTargetProperty p S).FullSubcategory

/-- perfectoid 条件を忘れ、元の S 上の環を取り出す。 -/
abbrev perfectoidTargetInclusion (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :
    PerfUnder_u p S ⥤ Under S := (perfectoidTargetProperty p S).ι

/-- perfectoid 標的の R 作用は R → S → T の合成で定める。 -/
def targetAlgebra (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (S : A_R R) :
    PerfUnder_u p S.right ⥤ A_R R :=
  perfectoidTargetInclusion p S.right ⋙ Under.map S.hom

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end Setup

/-! ## 界面で用いる導来対象・辺・自然変換

概要：離散代数の埋め込み の離散埋め込みと 導来ホモトピー圏の比較 の同値を界面の名前空間へ包装する。
方針：頂点・辺を評価し、整数次数のコホモロジーを通常の導来圏で取る。
規約：自然変換は区間との積からの単体的射である。
使われ方：E3 の単位、H⁰ の環構造、制限した標的図式。
-/

@[expose] public noncomputable section LimitData

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable (R : Type u) [CommRing R]

/-- 指定された S → T を R 上の代数の射として使う。 -/
def targetUnitMap (p : ℕ) [Fact p.Prime] (S : A_R R) (T : PerfUnder_u p S.right) :
    S ⟶ (targetAlgebra R p S).obj T := Under.homMk T.obj.hom rfl

/-- S から perfectoid 標的への射は標的圏の射について自然。 -/
theorem targetUnitMap_naturality (p : ℕ) [Fact p.Prime] (S : A_R R)
    {T U : PerfUnder_u p S.right} (f : T ⟶ U) :
    targetUnitMap R p S T ≫ (targetAlgebra R p S).map f = targetUnitMap R p S U := by
  ext1
  exact Under.w f.hom

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end LimitData

/-! ## 通常の商図式からの単体的 excision 四角形

概要：元の四辺とその可換性を、二つの二単体として同時に保持する。
方針：通常の nerve の合成二単体を対角で貼り、単体的関手で写す。
規約：右下は通常の商 T/IT。導来テンソル積には置き換えない。
使われ方：E3 界面の excision 欄。
-/

@[expose] public noncomputable section ExcisionDiagram

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R]

/-- 通常の商環に、元の構造射を通した R 作用を与える。 -/
def quotientAlgebra (S : A_R R) (I : Ideal S.right) : A_R R :=
  Under.mk (S.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- 元の通常の商環への射。 -/
def quotientProjection (S : A_R R) (I : Ideal S.right) : S ⟶ quotientAlgebra R S I :=
  Under.homMk (CommRingCat.ofHom (Ideal.Quotient.mk I)) rfl

/-- 下辺は、指定した f から誘導される通常の商の射。 -/
def quotientComparison {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    quotientAlgebra R S I ⟶ quotientAlgebra R T (I.map f.right.hom) :=
  Under.homMk (CommRingCat.ofHom (Ideal.quotientMap (I.map f.right.hom)
    f.right.hom Ideal.le_comap_map)) (by
      change (S.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ _ = T.hom ≫ _
      rw [← Under.w f, Category.assoc, Category.assoc]
      congr 1)

/-- 四辺の可換性は、元の商の射と元の f についての等式。 -/
theorem quotientSquare_commutes {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    f ≫ quotientProjection R T (I.map f.right.hom) =
      quotientProjection R S I ≫ quotientComparison R f I := by
  ext1
  ext x
  rfl

/-- 既存 excision 入力と同じ階数1付値環への一意延長条件。 -/
def ArcOutside (p : ℕ) {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
    ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
    ∀ k : S.right →+* V, ¬ (I ≤ RingHom.ker k) →
      ∃! l : T.right →+* V, l.comp f.right.hom = k

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end ExcisionDiagram

/-! ## D(R) 上の perfectoid 化界面（E3）の型

概要：原典の各性質を、その根拠を導出するためのデータとともに束ねる。
方針：界面の型だけを宣言し、存在は主張しない。
規約：普遍性は離散時の環準同型の普遍性。全射性や Tor 消滅を欄に含めない。
使われ方：普遍単位と指定錐の比較 以降で既存の二入力を界面依存の定理として導く。
-/

