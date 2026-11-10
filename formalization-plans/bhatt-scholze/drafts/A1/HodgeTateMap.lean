-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.HodgeTateMap（仮。原典 §4.2 Construction 4.9・Lemma 4.10・Thm 4.11）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §2.1・§2.2、単位 A1-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTateAffineModel

-- 本ファイルは drafts/A2/DerivedPrismaticCohomology.lean（Poly 上の RΓ まで）、drafts/A0/CechAlexander.lean（C^•、`cechAlexanderAffine`）、drafts/Shared/{CosimplicialCupProduct,DeRhamPolynomial}.lean と本体の `HomologicalAlgebra/Cosimplicial/BocksteinClass` を使う。

/-!
# Hodge–Tate 比較の写像（BS 著者版 Construction 4.9、Lemma 4.10、Thm 4.11 の主張）

## 概要
R = (A/d)⟨X_1,…,X_r⟩ について、Ō_{R/A} の模型 H^*(Tot(C^•/dC^•))（A0 の Čech–Alexander 複体の mod d、cup 積、Bockstein β）に、
η^0 : R → H^0、η^1 : Ω^1_{R/(A/d)} → H^1（dX_j ↦ β(η^0 X_j)）を定め、Lemma 4.10（β(f)² = 0）のもとで de Rham 複体の普遍性により
dg 代数の射 η^* : Ω^*_{R/(A/d)} → H^*(Tot(C^•/d)) を得る。Thm 4.11（＝Thm 6.3）は η^* が同型であること。

## 方針
模型の上で定義する（D27）。向き付きなので捻り {i} は落とす（D28）。Rem 4.19 の小さい模型 `cechAlexanderAffine` を使う
（Constr 4.18 の大きい模型との一致は A0 の S3 の補題と cup 積・Bockstein の自然性）。

## 規約
H^*(Tot(C^•/d)) は R 代数（C^n/dC^n は R 代数）。定理の証明は A1-4（Prop 6.2 経由）。

## 使われ方
Thm 6.3・Cor 4.12（A1-4）、Cor 5.5（A1-3）、A2 の HT filtration、A5 の Lemma 8.6。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity SerrePositivity.Cosimplicial

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
variable (r : ℕ)

abbrev hodgeTateCohomology' (i : ℕ) := cohomology (reducedModel P hP r) i
abbrev htSequence := regularShortExact (htRings P hP r) (htGenerator P hP r) (htGenerator_nat P hP r)
  (htGenerator_regular P hP r) A (htBase P hP r)

def moduleCohomologyBridge (k : Type u) [CommRing k] (X : CosimplicialObject CommRingCat.{u})
    (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ X) (i : ℕ) :
    cohomology X i ≃+ ((AlgebraicTopology.alternatingCofaceMapComplex _).obj (toModules k X ι)).homology i := by
  refine (cohomologyEquivHomology X i).trans ?_
  sorry -- 加群から加法群への忘却はホモロジーを保つ

def bockstein (i : ℕ) : hodgeTateCohomology' P hP r i →+ hodgeTateCohomology' P hP r (i+1) := by
  let β := regularBockstein (htRings P hP r) (htGenerator P hP r) (htGenerator_nat P hP r)
    (htGenerator_regular P hP r) A (htBase P hP r) i
  exact (moduleCohomologyBridge A (reducedModel P hP r) _ (i+1)).symm.toAddMonoidHom.comp
    (β.hom.toAddMonoidHom.comp (moduleCohomologyBridge A (reducedModel P hP r) _ i).toAddMonoidHom)

/-- 概要：η^0 : R → H^0（R → C^0/dC^0 の合成）。
方針：R → C^0/dC^0 は A0 の `sec`。余輪体。
規約：環の射。
使われ方：H^* の R 代数構造、η^1。 -/
instance : CommRing (hodgeTateCohomology' P hP r 0) := by
  sorry -- 次数零の cohomology を二つの余面の等化部分環に移送。積は cohomologyCup
def htZeroCycles := ((reducedModel P hP r).map (SimplexCategory.δ (0 : Fin 2))).hom.eqLocus
  (((reducedModel P hP r).map (SimplexCategory.δ (1 : Fin 2))).hom)
def htZeroIso : hodgeTateCohomology' P hP r 0 ≃+* htZeroCycles P hP r := by
  sorry -- cohomologyEquivHomology の次数 0 では境界は零、cup は同じ項での積
def hodgeTateMapZero : affineAlgebra P r →+* hodgeTateCohomology' P hP r 0 :=
  (htZeroIso P hP r).symm.toRingHom.comp
    ((htSec P hP r ⦋0⦌).codRestrict _ (by sorry)) -- sec は余面に自然

/-- R 作用は η⁰ の像との左 cup 積。 -/
def htModuleData (i : ℕ) :
    { M : Module (affineAlgebra P r) (hodgeTateCohomology' P hP r i) //
      letI := M
      ∀ (a : affineAlgebra P r) (z : hodgeTateCohomology' P hP r i), a • z = cast (by simp) (cohomologyCup (reducedModel P hP r) (hodgeTateMapZero P hP r a) z) } := by
  sorry -- η⁰(a)∪z。cup の単位・結合・加法性と次数 0 の左単位律
abbrev htModule (i : ℕ) := (htModuleData P hP r i).val

local instance (i : ℕ) : Module (affineAlgebra P r) (hodgeTateCohomology' P hP r i) := htModule P hP r i

/-- 概要：η^1 : Ω^1_{R/(A/d)} → H^1、dX_j ↦ β(η^0 X_j)、R 線形に延ばす（Ω^1 は dX_j 上自由）。
方針：`DeRham.dX` の像を指定して線形に延ばす。
規約：原典の f dg ↦ f β(g)。
使われ方：η^*。 -/
abbrev formVars (r : ℕ) := ULift.{u} (Fin r)
local instance completedCoordinateRing (k : Type u) [CommRing k] (n : ℕ) :
    CommRing (DeRham.completedPoly k (formVars.{u} n) p) :=
  SerrePositivity.DerivedCompletion.principalCompletionCommRing _ _

abbrev affineForms (i : ℕ) := DeRham.completedForms (A ⧸ P.ideal) (formVars.{u} r) p i
def affineCoordinateIso : affineAlgebra P r ≃+* DeRham.completedPoly (A ⧸ P.ideal) (formVars.{u} r) p := by
  sorry -- X_j↦X_(up j) と逆の rename を p 完備化単位から延長
instance (i : ℕ) : Module (affineAlgebra P r) (affineForms P r i) :=
  Module.compHom _ (affineCoordinateIso P r).toRingHom
def degreeZeroForm : affineAlgebra P r ≃ₗ[affineAlgebra P r] affineForms P r 0 := by
  sorry -- Ω̂⁰ の基底 1 に係数を掛ける
abbrev affineD (i : ℕ) := DeRham.completedDeRhamD (A ⧸ P.ideal) (formVars.{u} r) p i
abbrev affineWedge {i j : ℕ} := @DeRham.completedWedge (A ⧸ P.ideal) _ (formVars.{u} r) _ _ p i j

def htOneData :
    { l : affineForms P r 1 →ₗ[affineAlgebra P r] hodgeTateCohomology' P hP r 1 //
      ∀ f g : affineAlgebra P r, l (f • affineD P r 0 (degreeZeroForm P r g)) =
        f • bockstein P hP r 0 (hodgeTateMapZero P hP r g) } := by
  sorry -- dX_j を β(η⁰ X_j) へ送り R 線形に延長。連続 Leibniz 則で d̂g の式を得る

def hodgeTateMapOne := (htOneData P hP r).val

/-- 概要：Lemma 4.10：β(η^0 f)² = 0（p = 2 でだけ非自明）。
方針：Prop 6.2 の affine 直線（r = 1）で H^2 = 0 から、関手性（X ↦ f）で一般へ。A1-4 で証明。
規約：次数付き可換性だけからは出ない（2β(f)² = 0 まで）。
使われ方：η^* の存在（de Rham 複体の普遍性の平方零の条件）。 -/
def BetaSquareZero : Prop := ∀ f : affineAlgebra P r,
  let x := bockstein P hP r 0 (hodgeTateMapZero P hP r f)
  cohomologyCup (reducedModel P hP r) x x = 0

theorem betaSquareZero_of_line (h₂ : Subsingleton (hodgeTateCohomology' P hP 1 2)) :
    BetaSquareZero P hP r := by
  sorry -- X↦f による H² の射で β(η⁰ X)∪β(η⁰ X)=0 を移す。
        -- cohomologyMap_cup と bockstein_natural、両模型は共通の Čech 模型で比較

theorem bockstein_sq_zero : BetaSquareZero P hP r := by
  sorry -- r=1 の η⁰・η¹ だけで得る H²=0 と X↦f の自然性。A1-4 でこの順に証明

/-- 概要：Constr 4.9：dg 代数の射 η^* : Ω^*_{R/(A/d)} → H^*(Tot(C^•/d))。
方針：`DeRham.exists_unique_dgHom` に η^0・η^1・`bockstein_sq_zero` を渡す。
規約：一意。
使われ方：Thm 4.11 の主張。 -/
structure HTAlgebraMap where
  app (i : ℕ) : affineForms P r i →ₗ[affineAlgebra P r] hodgeTateCohomology' P hP r i
  on_zero (f) : app 0 (degreeZeroForm P r f) = hodgeTateMapZero P hP r f
  on_one : app 1 = hodgeTateMapOne P hP r
  product {i j} (x : affineForms P r i) (y : affineForms P r j) :
    app (i+j) (affineWedge P r x y) = cohomologyCup (reducedModel P hP r) (app i x) (app j y)
  differential (i) (x : affineForms P r i) :
    app (i+1) (affineD P r i x) = bockstein P hP r i (app i x)

def hodgeTateMap : HTAlgebraMap P hP r := by
  sorry -- bockstein_sq_zero と cup の反交換性で η¹ の像の平方は零。
        -- DeRham.exists_unique_dgHom の外積の普遍性を完備自由形式へ延長
theorem hodgeTateMap_unique (f : HTAlgebraMap P hP r) : f = hodgeTateMap P hP r := by
  sorry -- dX の外積基底で η⁰・η¹ と一致

/-- 概要：Thm 4.11 ＝ Thm 6.3（多項式代数）：η^* は各次数で同型。特に H^i(Ō_{R/A}) ≅ Ω^i_{R/(A/d)}、i > r で零。
方針：A1-4（Prop 6.2 の一般の r）。
規約：基底は一般の有界向き付き prism（D30）。
使われ方：Cor 4.12、A2、A5。 -/
def HodgeTateIsoStatement : Prop := ∀ i, Function.Bijective ((hodgeTateMap P hP r).app i)

/-- 概要：Cor 4.12：Δ_{R/A} の形成は有界 prism の任意の底変換と可換（Tor 振幅の仮定なし）。
方針：導来 Nakayama で mod d に帰着し、Thm 6.3 と微分形式の底変換から。
規約：A0 の Lemma 4.20 の仮定を外した形。
使われ方：Construction 7.6 の底変換（A2）。 -/
abbrev polynomialDelta (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) :=
  (prismCompleteInclusion P).app _ (prismaticCohomologyCAlg P hP r)

/-- 同じ変数を送る A0 の項ごとの射による Tot の比較。係数を先に延長してから P′ で完備化する。 -/
def polynomialChangeEdge {A' : Type u} [CommRing A'] (P' : OrientedPrism p A') (hP' : IsBoundedPrism P')
    (f : OrientedPrism.Hom P P') :
    SSet.Edge ((cAlgBaseChange f.toRingHom ≫ prismCompletion P').app _ (polynomialDelta P hP r))
      (prismaticCohomologyCAlg P' hP' r) := by
  sorry -- cechAlexanderAffine_baseChange の標準脚に沿う Tot 射を係数拡大と完備反射の随伴で移す

def PrismaticCohomologyBaseChangeStatement {A' : Type u} [CommRing A']
    (P' : OrientedPrism p A') (hP' : IsBoundedPrism P') (f : OrientedPrism.Hom P P') : Prop :=
  IsIso (HomotopyCategory.homMk (polynomialChangeEdge P hP r P' hP' f))

end SerrePositivity.BhattScholze.Prismatic
