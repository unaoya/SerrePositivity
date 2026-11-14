module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCompletedSubstitution
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawPolynomialSubstitution
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech

/-!
# 分冪係数の多項式代入の関手性

## 概要
小さい模型への多項式代入は、未完備でも完備化後でも厳密な関手を定める。

## 方針
各頂点での未完備の代入の恒等式を、項ごとの完備化に移す。

## 規約
基底は p 正則かつ p 完備。

## 使われ方
BS 著者版 Theorem 6.4 の pd de Rham の第 0 行。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))
variable {Q Q' : Poly k} (f : Q ⟶ Q')

/-- 小さい未完備模型の各項の代入は、余面および余退化と可換。 -/
def rawSubstitution : pdRawModel k Q.n ⟶ pdRawModel k Q'.n where
  app n := Under.homMk
    (CommRingCat.ofHom (substitute p γ hk hr f n.len).toRingHom) (by
      apply CommRingCat.hom_ext
      exact RingHom.ext (substitute p γ hk hr f n.len).commutes)
  naturality {m n} θ := by
    apply Under.UnderMorphism.ext
    exact congrArg (fun e : pdRaw k Q.n m.len →ₐ[k] pdRaw k Q'.n n.len =>
      CommRingCat.ofHom e.toRingHom) (substitute_naturality p γ hk hr f θ)

/-- 余単体的な未完備分冪模型を多項式代入について関手化する。 -/
def rawSubstitutionFunctor : Poly k ⥤ SerrePositivity.Cosimplicial.CosimplicialAlgebra k where
  obj Q := pdRawModel k Q.n
  map f := rawSubstitution p γ hk hr f
  map_id Q := by
    ext n : 1
    apply Under.UnderMorphism.ext
    exact congrArg (fun e : pdRaw k Q.n n.len →ₐ[k] pdRaw k Q.n n.len =>
      CommRingCat.ofHom e.toRingHom) (substitute_id p γ hk hr Q n.len)
  map_comp {Q₁ Q₂ Q₃} f g := by
    ext n : 1
    apply Under.UnderMorphism.ext
    exact congrArg (fun e : pdRaw k Q₁.n n.len →ₐ[k] pdRaw k Q₃.n n.len =>
      CommRingCat.ofHom e.toRingHom) (substitute_comp p γ hk hr f g n.len)

/-- 小さい完備分冪模型を多項式代入について関手化する。 -/
def completedSubstitutionFunctor : Poly k ⥤ SerrePositivity.Cosimplicial.CosimplicialAlgebra k :=
  rawSubstitutionFunctor p γ hk hr ⋙
    (Functor.whiskeringRight SimplexCategory _ _).obj (principalCompletionUnder p (CommRingCat.of k))

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
