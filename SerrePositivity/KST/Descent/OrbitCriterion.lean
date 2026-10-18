module

public import SerrePositivity.KST.Descent.OrbitComparisonCube

/-!
# 実際の軌道比較から全次数の降下比較へ

## 概要
構成済みの軌道正方形の中項・例外部分の固定比較が全次数同型なら、
元の射 p の指定された全次数降下比較が全単射になることを証明する。

## 方針
自然な blowup 列へ同変立方体を適用し、不変部分で全次数の五項補題を使う。
自明作用の不変部分と、前層の固定部分の二つの記述を指定同型で移す。

## 規約
中項の比較は (3.8)、例外部分の比較は中心上の帰納から供給する責務が残る。
この定理を最小公理 (1)–(8) からの定理 3.1 全体の完成とは数えない。

## 使われ方
論文 定理 3.1 の実際の軌道正方形と、公開する π_* 版 PiDescent の接続。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent.NaturalBlowupSequences

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable {Coefficient : Type w}
variable {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}

/-- 概要：軌道正方形の二つの固定比較から実際の全次数降下を得る（定理 3.1）。
方針：不変部分の列の五項補題の結論を、基底の自明作用と指定引き戻しの同定で移す。
規約：任意の係数・全整数次数を保持し、無関係な抽象同型には置き換えない。
使われ方：(3.8) と中心上の帰納仮定を供給した後の軌道段階。 -/
theorem orbit_piDescent_of_fixed_components (data : NaturalBlowupSequences L)
    [IsReduced V.obj.left] {G : Type*} [Group G] [Finite G] [MulAction G I]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ)
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)
    (product_comparison : ∀ H n, Function.Bijective
      ((data.orbitFixedComparison p sections section_identity covering
        action over_base equivariant H).mapB n))
    (exceptional_comparison : ∀ H n, Function.Bijective
      ((data.orbitFixedComparison p sections section_identity covering
        action over_base equivariant H).mapC n)) :
    L.PiDescent p action over_base := by
  intro H n
  let f := data.orbitFixedComparison p sections section_identity covering
    action over_base equivariant H
  have hf : Function.Bijective (f.mapA n) :=
    f.bijective_mapA (product_comparison H) (exceptional_comparison H) n
  let source := trivialInvariantsEquiv (L.pullbackRepresentation H n (1 : G →* Aut B))
  let target := L.invariantSubmoduleEquiv H n action
  have comparison :
      (fun x ↦ target.symm (f.mapA n (source.symm x))) =
        L.invariantComparison H n p action over_base := by
    funext x
    apply Subtype.ext
    rfl
  rw [← comparison]
  exact target.symm.bijective.comp (hf.comp source.symm.bijective)

end SerrePositivity.KST.Descent.NaturalBlowupSequences
