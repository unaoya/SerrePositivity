-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.HodgeTateMap（仮。原典 §4.2 Construction 4.9・Lemma 4.10・Thm 4.11）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §2.1・§2.2、単位 A1-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTateOneDerivative
import all SerrePositivity.BhattScholze.Prismatic.HodgeTateOneDerivative

public import SerrePositivity.BhattScholze.Prismatic.HodgeTateBocksteinSquare
public import SerrePositivity.BhattScholze.Prismatic.HodgeTateAffineForms

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

-- η⁰ と Bockstein は本体の HodgeTateZero に置く。

-- R 作用は本体の HodgeTateModule に置く。

local instance (i : ℕ) : Module (affineAlgebra P r) (hodgeTateCohomology' P hP r i) := htModule P hP r i

-- affineForms、degreeZeroForm と完備微分・外積は本体の HodgeTateAffineForms に置く。

def htOneData :
    { l : affineForms P r 1 →ₗ[affineAlgebra P r] hodgeTateCohomology' P hP r 1 //
      ∀ f g : affineAlgebra P r, l (f • affineD P r 0 (degreeZeroForm P r g)) =
        f • (bockstein P hP r 0 (hodgeTateMapZero P hP r g) : hodgeTateCohomology' P hP r 1) } :=
  ⟨hodgeTateMapOne P hP r, fun f g => by
    change _ = f • htBocksteinZero P hP r g
    exact hodgeTateMapOne_smul_d P hP r f g⟩

-- BetaSquareZero と bockstein_sq_zero は本体の HodgeTateBocksteinSquare に置く。
-- p = 2 の場合は δ による余境界で直接証明する。

theorem betaSquareZero_of_line (_h₂ : Subsingleton (hodgeTateCohomology' P hP 1 2)) :
    BetaSquareZero P hP r :=
  bockstein_sq_zero P hP r

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
