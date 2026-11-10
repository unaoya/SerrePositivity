module
public import SerrePositivity.KST.ProExcision.EquivariantStrictification
public import SerrePositivity.KST.ProExcision.BarAction
public import SerrePositivity.KST.ProExcision.ConjugationNaturality

/-!
# Construction A.5 の非可換標的の因子化データ

概要：二つの入力ホモトピーの値域を P、Q に保ち、最後に μ:P×Q→H へ送る。
方針：μ、α、β と外部 G の作用の可換条件を明示する。
規約：原典 KST Construction A.5 の一般文言からの変更（正本 §13-14）。
像の可換性だけを入力にせず、因子内のホモトピーを要求する。
右辺は A.5 の右辺の augmentation 補正 C(φ)+C(φ′)−C(e_H)。
使われ方：非可換ブロック行列群に対する Lemma 4.16。H、I の可換性は仮定しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
variable {T P Q H : Type u} [Group T] [Group P] [Group Q] [Group H]

/-- 概要：非可換標的の A.5 で用いる積を経由する群準同型。
方針：μ、α、β を独立した数学的データにする。
規約：KST A.5 の一般文言を正本 §13-14 に従って修正。
使われ方：ホモトピーの値域を群の積に保ってから μ を適用する。 -/
structure GroupProductData (T P Q H : Type u) [Group T] [Group P] [Group Q] [Group H] where
  μ : P × Q →* H
  α : T →* P
  β : T →* Q

/-- 概要：第一因子からの φ。
方針：α と Q の単位の対に μ を適用。
規約：KST A.5 の修正形。使われ方：補正和の第一項。 -/
def GroupProductData.left (d : GroupProductData T P Q H) : T →* H :=
  d.μ.comp (d.α.prod (1 : T →* Q))

/-- 概要：第二因子からの φ′。
方針：P の単位と β の対に μ を適用。
規約：KST A.5 の修正形。使われ方：補正和の第二項。 -/
def GroupProductData.right (d : GroupProductData T P Q H) : T →* H :=
  d.μ.comp ((1 : T →* P).prod d.β)

/-- 概要：φ·φ′ の実際の群準同型。
方針：対 (α,β) と μ を合成。
規約：H の可換性を要求しない。使われ方：KST A.5 の左辺。 -/
def GroupProductData.product (d : GroupProductData T P Q H) : T →* H :=
  d.μ.comp (d.α.prod d.β)

/-- 概要：積を経由する準同型は因子の像の積に分解する。
方針：(p,q)=(p,1)(1,q) の μ による像を取る。
規約：KST A.5、非可換標的。使われ方：φ·φ′ の同定。 -/
lemma GroupProductData.product_apply (d : GroupProductData T P Q H) (t : T) :
    d.product t = d.left t * d.right t := by
  change d.μ (d.α t, d.β t) = d.μ (d.α t, 1) * d.μ (1, d.β t)
  rw [← map_mul]
  simp

/-- 概要：μ の両因子の像は互いに可換。
方針：直積群内での可換性を μ で送る。
規約：入力ホモトピーも P、Q 内にあることが別に必要。
使われ方：KST A.5 と Lemma 4.16 の積の解釈。 -/
lemma GroupProductData.images_commute (d : GroupProductData T P Q H) (p : P) (q : Q) :
    Commute (d.μ (p, 1)) (d.μ (1, q)) := by
  change d.μ (p, 1) * d.μ (1, q) = d.μ (1, q) * d.μ (p, 1)
  rw [← map_mul, ← map_mul]
  simp

/-- 概要：離散群の準同型の非被約自由整数加群への写像。
方針：一対象群圏の nerve を自由化する。
規約：KST App. A の C(f)。使われ方：A.5 の因子内の両端。 -/
def groupLinearizedMap {U V : Type u} [Group U] [Group V] (f : U →* V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj U)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj V)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (nerveMap (SingleObj.mapHom U V f))

/-- 概要：離散モノイドの作用から分類空間への集合の作用を作る。
方針：各次数で nerve の射列に自己準同型を適用する。
規約：KST A.5・A.6 の外部 G、区間因子は固定。
使われ方：離散群のホモトピーの同変性の実際の界面。 -/
def discreteNerveAction (G U : MonCat.{u}) (ρ : G →* Monoid.End U) :
    SimplicialSetAction ((Functor.const SimplexCategoryᵒᵖ).obj G) (nerve (SingleObj U)) where
  action n := monoidNerveAction G U ρ n.unop.len
  naturality _ _ _ := rfl

variable {G : Type u} [Monoid G]

/-- 概要：積による因子化と外部 G の作用の可換条件。
方針：α、β、μ それぞれに同変性を要求する。
規約：KST A.5 の修正形。証明すべき比較の結論を含まない。
使われ方：最後の μ の適用まで G 同変性を保つ。 -/
structure EquivariantGroupProductData (ρT : G →* Monoid.End T)
    (ρP : G →* Monoid.End P) (ρQ : G →* Monoid.End Q) (ρH : G →* Monoid.End H)
    extends GroupProductData T P Q H where
  α_equivariant (a : G) (t : T) : α (ρT a t) = ρP a (α t)
  β_equivariant (a : G) (t : T) : β (ρT a t) = ρQ a (β t)
  μ_equivariant (a : G) (p : P) (q : Q) : μ (ρP a p, ρQ a q) = ρH a (μ (p, q))

/-- 概要：A.5 の二つの因子内の同変 m 次ホモトピーの入力。
方針：第一入力は C(P)、第二入力は C(Q) に値を持たせる。
規約：正本 §13-14 の採用形。原典の像の可換性だけの条件からの変更であり、
結論の (m+m′+1) 次ホモトピーを仮定に含めない。
使われ方：厳密化・正規化・AW/shuffle 比較に渡すデータ。 -/
structure ConstructionA5Input {ρT : G →* Monoid.End T} {ρP : G →* Monoid.End P}
    {ρQ : G →* Monoid.End Q} {ρH : G →* Monoid.End H}
    (d : EquivariantGroupProductData ρT ρP ρQ ρH) (m m' : ℕ) where
  first : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap d.α) (groupLinearizedMap (1 : T →* P)) m
  second : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap d.β) (groupLinearizedMap (1 : T →* Q)) m'
  first_equivariant : LinearizedCylinderEquivariant
    (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
    (discreteNerveAction (MonCat.of G) (MonCat.of P) ρP) first.h
  second_equivariant : LinearizedCylinderEquivariant
    (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
    (discreteNerveAction (MonCat.of G) (MonCat.of Q) ρQ) second.h

/-- 概要：分類空間を自由化した写像は群の同変準同型から同変性を受け取る。
方針：自由加群の基底と nerve の各射ラベルで入力の等式を使う。
規約：KST A.5・A.6 の外部 G。使われ方：厳密化の同変性への接続。 -/
lemma groupLinearizedMap_equivariant {U V : Type u} [Group U] [Group V]
    (ρU : G →* Monoid.End U) (ρV : G →* Monoid.End V) (f : U →* V)
    (hf : ∀ a x, f (ρU a x) = ρV a (f x)) :
    LinearizedEquivariant (discreteNerveAction (MonCat.of G) (MonCat.of U) ρU)
      (discreteNerveAction (MonCat.of G) (MonCat.of V) ρV) (groupLinearizedMap f) := by
  intro n a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro p
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom U V f)).app n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (↾fun p ↦ p ⋙ SingleObj.mapHom U U (ρU a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (↾fun p ↦ p ⋙ SingleObj.mapHom V V (ρV a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom U V f)).app n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator
  apply (SerrePositivity.KST.Comparison.monoidWordEquiv (MonCat.of V) n.unop.len).injective
  funext i
  exact hf a _

variable {ρT : G →* Monoid.End T} {ρP : G →* Monoid.End P}
variable {ρQ : G →* Monoid.End Q} {ρH : G →* Monoid.End H}

/-- 概要：第一因子からの φ は外部 G 同変。
方針：α と μ の同変性と自己準同型の単位保存を使う。
規約：KST A.5 の修正形。使われ方：補正和の同変性。 -/
lemma EquivariantGroupProductData.left_equivariant
    (d : EquivariantGroupProductData ρT ρP ρQ ρH) (a : G) (t : T) :
    d.toGroupProductData.left (ρT a t) = ρH a (d.toGroupProductData.left t) := by
  change d.μ (d.α (ρT a t), 1) = ρH a (d.μ (d.α t, 1))
  rw [d.α_equivariant]
  simpa only [map_one] using d.μ_equivariant a (d.α t) 1

/-- 概要：第二因子からの φ′ は外部 G 同変。
方針：β と μ の同変性と単位保存を使う。
規約：KST A.5 の修正形。使われ方：補正和の同変性。 -/
lemma EquivariantGroupProductData.right_equivariant
    (d : EquivariantGroupProductData ρT ρP ρQ ρH) (a : G) (t : T) :
    d.toGroupProductData.right (ρT a t) = ρH a (d.toGroupProductData.right t) := by
  change d.μ (1, d.β (ρT a t)) = ρH a (d.μ (1, d.β t))
  rw [d.β_equivariant]
  simpa only [map_one] using d.μ_equivariant a 1 (d.β t)

/-- 概要：φ·φ′ の準同型も外部 G 同変。
方針：対 (α,β) と μ の同変性を合成する。
規約：KST A.5 の修正形、H の可換性は不要。
使われ方：左辺の線形化写像の同変性。 -/
lemma EquivariantGroupProductData.product_equivariant
    (d : EquivariantGroupProductData ρT ρP ρQ ρH) (a : G) (t : T) :
    d.toGroupProductData.product (ρT a t) = ρH a (d.toGroupProductData.product t) := by
  change d.μ (d.α (ρT a t), d.β (ρT a t)) = ρH a (d.μ (d.α t, d.β t))
  rw [d.α_equivariant, d.β_equivariant, d.μ_equivariant]

/-- 概要：A.5 の第一入力の因子内での厳密化は G 同変。
方針：α の自由化と入力区間写像の同変性を厳密化補題へ渡す。
規約：KST A.5 の修正形、値域は C(P)。使われ方：正規化前の第一因子。 -/
lemma ConstructionA5Input.first_strictified_equivariant
    {d : EquivariantGroupProductData ρT ρP ρQ ρH} {m m' : ℕ}
    (h : ConstructionA5Input d m m') :
    LinearizedEquivariant (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
      (discreteNerveAction (MonCat.of G) (MonCat.of P) ρP) h.first.strictifiedMap :=
  h.first.strictifiedMap_equivariant
    (groupLinearizedMap_equivariant ρT ρP d.α d.α_equivariant) h.first_equivariant

/-- 概要：A.5 の第二入力の因子内での厳密化は G 同変。
方針：β の自由化と入力区間写像の同変性を厳密化補題へ渡す。
規約：KST A.5 の修正形、値域は C(Q)。使われ方：正規化前の第二因子。 -/
lemma ConstructionA5Input.second_strictified_equivariant
    {d : EquivariantGroupProductData ρT ρP ρQ ρH} {m m' : ℕ}
    (h : ConstructionA5Input d m m') :
    LinearizedEquivariant (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
      (discreteNerveAction (MonCat.of G) (MonCat.of Q) ρQ) h.second.strictifiedMap :=
  h.second.strictifiedMap_equivariant
    (groupLinearizedMap_equivariant ρT ρQ d.β d.β_equivariant) h.second_equivariant

end SerrePositivity.KST.ProExcision

