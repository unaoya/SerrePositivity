module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ReesMap
public import SerrePositivity.AlgebraicGeometry.ProjMap

/-!
概要：KST §5 の通常の blowup の係数環に関する比較射。
方針：Rees 代数の次数付き係数写像へ Proj の反変関手を適用する。
規約：この比較射と、一般の基底変更による同型を区別する。
使われ方：局所化との両立と、導来 blowup の underlying scheme との幾何学的比較。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)

/--
概要：像イデアルの blowup から元の blowup への自然な比較射。
方針：Rees 代数の係数写像と irrelevant ideal の包含から Proj の射を得る。
規約：KST §5、任意の環準同型に対する射であり、一般に同型とは主張しない。
使われ方：局所化での貼り合わせと基底変更後の通常 blowup の比較。
-/
def affineBlowupBaseMap : affineBlowup (I.map f) ⟶ affineBlowup I :=
  Proj.map (reesGradedMap I (I.map f) f le_rfl) (reesGradedMap_irrelevant_le I f)

set_option backward.isDefEq.respectTransparency false in
/--
概要：係数環による blowup の比較射は基底の Spec の射と両立する。
方針：Proj の零次成分上の構造射の自然性と係数写像を合成する。
規約：KST §5、両辺は Spec R への実際の射。
使われ方：局所化による開基底変更への比較。
-/
@[reassoc] theorem affineBlowupBaseMap_base :
    affineBlowupBaseMap I f ≫ affineBlowupπ I =
      affineBlowupπ (I.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  unfold affineBlowupBaseMap affineBlowupπ
  rw [← Category.assoc, proj_map_toSpecZero]
  simp only [Category.assoc, ← Spec.map_comp]
  congr 2
  ext r : 2
  apply Subtype.ext
  apply Subtype.ext
  change (Polynomial.C r).map f = Polynomial.C (f r)
  exact Polynomial.map_C f

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
