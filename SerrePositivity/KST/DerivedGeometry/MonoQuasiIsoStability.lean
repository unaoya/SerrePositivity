module

public import SerrePositivity.KST.DerivedGeometry.ColimitMapStability
public import SerrePositivity.KST.DerivedGeometry.ExactColimitQuasiIso
public import SerrePositivity.KST.DerivedGeometry.MonoQuasiIsoPushout
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms

/-!
概要：Grothendieck アーベル圏の非有界単射準同型の cell 構成での安定性。
方針：完全な余極限の準同型保存、押し出しの余核比較、単射の既存の安定性を組み合わせる。
規約：各項 injective という条件に置換しない。
使われ方：Stacks 19.12.4・19.12.6、TT §3・§8、Toën §3.2 の非有界分解の超限工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits MorphismProperty
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C]

/--
概要：完全な余極限は準同型の射の性質を保つ。
方針：選ばれた colimMap の準同型性から任意の余極限の比較へ移す。
規約：非有界複体。
使われ方：Stacks Theorem 19.12.6、TT §3 の極限順序数での準同型性。
-/
instance quasiIso_isStableUnderExactColimitsOfShape
    (J : Type*) [Category* J] [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    (HomologicalComplex.quasiIso C (.up ℤ)).IsStableUnderColimitsOfShape J :=
  stableUnderColimits_of_colimMap _ (fun f hf =>
    quasiIso_colimMap_of_exactColimits (.up ℤ) f (fun j => hf j))

/--
概要：非有界複体の単射準同型の射の性質。
方針：単射と準同型の共通部分を取る。
規約：元の複体の圏。
使われ方：Stacks 19.12.6、TT §3 の cell 遷移。
-/
def monicQuasiIsomorphisms : MorphismProperty (CochainComplex C ℤ) :=
  monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)

/--
概要：単射準同型は押し出しで保たれる。
方針：単射性の既存の保存と準同型性の余核による証明を組み合わせる。
規約：任意のアーベル圏。
使われ方：Stacks 19.12.4・19.12.6、TT §3 の cell 付加。
-/
instance monicQuasiIsomorphisms_cobaseChange : (monicQuasiIsomorphisms (C := C)).IsStableUnderCobaseChange where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    have : Mono f := hf.1
    have : QuasiIso f := hf.2
    exact ⟨(monomorphisms (CochainComplex C ℤ)).of_isPushout sq hf.1,
      quasiIso_of_isPushout_of_mono sq.flip⟩

variable [IsGrothendieckAbelian.{w} C]

/--
概要：非有界複体の準同型は小さい filtered colimit で保たれる。
方針：AB5 と完全な余極限での保存を使う。
規約：Grothendieck 性の宇宙に合わせる。
使われ方：Stacks Theorem 19.12.6、TT §3 の超限極限。
-/
instance quasiIso_filteredColimits :
    IsStableUnderFilteredColimits.{w, w} (HomologicalComplex.quasiIso C (.up ℤ)) where
  isStableUnderColimitsOfShape J := inferInstance

/--
概要：非有界複体の準同型は小さい coproduct で保たれる。
方針：AB4 と完全な離散余極限での保存を使う。
規約：Grothendieck 性から AB4 を得る。
使われ方：Stacks Lemma 19.12.4、TT §3 の cell の同時付加。
-/
instance quasiIso_coproducts : IsStableUnderCoproducts.{w} (HomologicalComplex.quasiIso C (.up ℤ)) where
  isStableUnderCoproductsOfShape J := inferInstance

end SerrePositivity.KST.DerivedGeometry
