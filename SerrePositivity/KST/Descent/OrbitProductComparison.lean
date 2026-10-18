module

public import SerrePositivity.KST.Descent.OrbitCriterion
public import SerrePositivity.KST.Descent.OrbitCoproduct
public import SerrePositivity.KST.Descent.FixedPullbackComparison

/-!
# (3.8) と中心上の降下から実際の中項比較へ

## 概要
軌道の比較立方体の中項の固定比較を、コピー側の (3.8) と中心上の降下から証明する。

## 方針
実際の fold の降下と中心の第二射影の降下を、同変写像の不変部分の比較に移す。
積の不変部分の同定で二つの全単射を組み合わせる。

## 規約
非交和の値の有限積保存は Zariski 降下から供給すべき条件。
中心上の降下と例外部分の比較の証明は、残る帰納・コピー分解の責務。

## 使われ方
論文 定理 3.1 の実際の軌道正方形の全次数の貼り合わせ。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace SerrePositivity.KST.Descent.NaturalBlowupSequences

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable {Coefficient : Type w}
variable {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}

/-- 概要：(3.8) と中心上の降下から軌道比較の中項は全次数同型（定理 3.1）。
方針：実際の fold と中心の第二射影の指定比較を積の不変部分へ移す。
規約：中項全体の同型性を追加仮定にせず、コピーの普遍性と中心上の仮定から導く。
使われ方：実際の軌道比較の五項補題の一つの入力。 -/
theorem orbitProductComparison_bijective (data : NaturalBlowupSequences L)
    [∀ H n, PreservesLimit (Discrete.functor (fun _ : I ↦ op B)) (L H n)]
    [IsReduced V.obj.left] {G : Type*} [Group G] [Finite G] [MulAction G I]
    [MulAction.IsPretransitive G I] [Nonempty I]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ)
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)
    (center_descent : L.PiDescent
      (closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)))
      (orbitCenterAction p sections action over_base)
      (orbitCenterProjection_invariant p sections action over_base)) (H : Coefficient) (n : ℤ) :
    Function.Bijective ((data.orbitFixedComparison p sections section_identity covering
      action over_base equivariant H).mapB n) := by
  have fold_descent := orbitFold_piDescent_of_preservesProduct p sections section_identity L
    action over_base equivariant
  have fold_bijective := L.fixedPullbackIntertwining_bijective H n
    (orbitFold p sections section_identity)
    (orbitAction p sections section_identity action equivariant)
    (orbitFold_invariant p sections section_identity action over_base equivariant)
    (fold_descent H n)
  have center_bijective := L.fixedPullbackIntertwining_bijective H n
    (closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)))
    (orbitCenterAction p sections action over_base)
    (orbitCenterProjection_invariant p sections action over_base) (center_descent H n)
  exact invariantMap_product_bijective _ _ fold_bijective center_bijective

/-- 概要：中心上の降下と例外部分の固定比較から実際の軌道段階の降下（定理 3.1）。
方針：中項の比較を (3.8) と中心上の降下から構成し、全次数の軌道判定に入力する。
規約：例外部分のコピー分解と中心上の帰納の供給は残る。
使われ方：最小公理からの定理 3.1 の帰納の接続点。 -/
theorem orbit_piDescent_of_center_and_exceptional (data : NaturalBlowupSequences L)
    [∀ H n, PreservesLimit (Discrete.functor (fun _ : I ↦ op B)) (L H n)]
    [IsReduced V.obj.left] {G : Type*} [Group G] [Finite G] [MulAction G I]
    [MulAction.IsPretransitive G I] [Nonempty I]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ)
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)
    (center_descent : L.PiDescent
      (closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)))
      (orbitCenterAction p sections action over_base)
      (orbitCenterProjection_invariant p sections action over_base))
    (exceptional_comparison : ∀ H n, Function.Bijective
      ((data.orbitFixedComparison p sections section_identity covering
        action over_base equivariant H).mapC n)) :
    L.PiDescent p action over_base :=
  data.orbit_piDescent_of_fixed_components p sections section_identity covering
    action over_base equivariant
    (data.orbitProductComparison_bijective p sections section_identity covering
      action over_base equivariant center_descent) exceptional_comparison

end SerrePositivity.KST.Descent.NaturalBlowupSequences
