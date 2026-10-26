module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullDiagonalTerminal
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullHom
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalVertices
public import SerrePositivity.InfinityCategories.Core.UniverseInitialTerminal
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
/-!
概要：固定 dg 零合成の全成分を、実区間 Hom 比較の始域に保持する。
方針：元の終対象部分複体の宇宙持ち上げを、豊穣 Hom の全部分複体と同定する。
規約：高次単体を保持し、元の共有対角を変更しない。
使われ方：同じ零成分の二つの実対角比較のホモトピー類の一意性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : DGGluingMilnorSquare R d)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local instance : ∀ X Y : StableQCat.{u + 1}, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y => stableQCat_sHom_kanComplex X Y
local instance : KanComplex ((SSet.uliftFunctor.{u + 2, u + 1}).obj
    (SimplicialCategory.sHom (C := StableQCat.{u + 1}) (K) (B))) := by
  letI : KanComplex (SimplicialCategory.sHom (C := StableQCat.{u + 1}) (K) (B)) :=
    stableQCat_sHom_kanComplex (K) (B)
  exact kanComplex_uliftFunctor_obj _
/-- 概要：元実豊穣 Hom の零完全関手だけからなる全成分。
方針：元の完全関手圏での終対象性を全部分複体の頂点条件とする。
規約：元の実 Hom の全部分複体。使われ方：共有対角比較の一意性。 -/
abbrev DGOdotMilnorNuNullIntervalComponent : SSet.{u + 2} :=
  fullSubcomplexOnVertices ((SSet.uliftFunctor.{u + 2, u + 1}).obj
    (SimplicialCategory.sHom (C := StableQCat.{u + 1}) (K) (B)))
      (fun x => IsTerminalVertex x.down.val)
/-- 概要：同じ零成分は元の可縮全比較空間の宇宙持ち上げと厳密に同型。
方針：core の値と二つの頂点条件を同じ元完全関手へ戻す。
規約：全次数の同型。使われ方：元区間 Hom 内の零成分の制御。 -/
def dgOdotMilnorNuNullIntervalComponentIso (h : DGGluingMilnorSquare R d) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (DGOdotMilnorNuNullCoherenceSpace R d) ≅
      DGOdotMilnorNuNullIntervalComponent R d where
  hom := fullSubcomplexLift _
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (dgOdotMilnorNuNullCoherenceHom R d h))
    (fun x => fullSubcomplexOnVertices_vertex x.down)
  inv :=
    { app n := ↾fun x => ULift.up ⟨x.val.down.val, fun α => x.property α⟩
      naturality n m α := by
        apply ConcreteCategory.hom_ext
        intro x
        apply ULift.ext
        apply Subtype.ext
        rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    rfl
/-- 概要：同じ実区間 Hom の零成分は全境界を充填する。
方針：元可縮空間の全頂点の終対象性を持ち上げ、同じ全次数同型で移す。
規約：単なる連結性へ弱めない。使われ方：指定端点を保つ比較の一意性。 -/
lemma dgOdotMilnorNuNullIntervalComponent_contractible (h : DGGluingMilnorSquare R d) :
    IsContractibleKan (DGOdotMilnorNuNullIntervalComponent R d) := by
  apply isContractibleKan_of_iso (dgOdotMilnorNuNullIntervalComponentIso R d h)
  apply isContractibleKan_of_nonempty_of_all_terminal
  · exact ⟨ULift.up
      (Classical.choice (dgOdotMilnorNuNullCoherenceSpace_contractible R d h).nonempty)⟩
  · intro x
    exact (isTerminalVertex_iff_ulift x.down).mp
      ((dgOdotMilnorNuNullCoherenceSpace_contractible R d h).isTerminalVertex x.down)
/-- 概要：同じ零成分から実両端固定区間 Hom への元の標準比較。
方針：実 Hom の全部分複体包含と標準 coherent 比較を合成する。
規約：元の指定比較射。使われ方：共有対角の全ホモトピー類の比較。 -/
def dgOdotMilnorNuNullIntervalComponentMap :
    DGOdotMilnorNuNullIntervalComponent R d ⟶
      intervalMappingSpace (stableVertex (K)) (stableVertex (B)) :=
  (fullSubcomplexOnVertices ((SSet.uliftFunctor.{u + 2, u + 1}).obj
    (SimplicialCategory.sHom (C := StableQCat.{u + 1}) (K) (B)))
      (fun x => IsTerminalVertex x.down.val)).ι ≫
    coherentHomIntervalComparison (C := StableQCat.{u + 1}) (K) (B)
/-- 概要：同じ零成分の標準実区間 Hom 比較は充満忠実。
方針：全部分複体の充満忠実性と標準 Hom 同値を合成する。
規約：元の全比較射。使われ方：実対角二比較の同じ類への回収。 -/
lemma dgOdotMilnorNuNullIntervalComponentMap_isFullyFaithful :
    IsFullyFaithful (dgOdotMilnorNuNullIntervalComponentMap R d) :=
  (isFullyFaithful_fullSubcomplexOnVertices_ι _ _).comp
    (coherentHomIntervalComparison_isQCatEquivalence (C := StableQCat.{u + 1}) 
      (K) (B)).isFullyFaithful
/-- 概要：同じ元零成分の二頂点の間では、実区間比較の射の類は一意。
方針：全比較の充満忠実性で元可縮空間へ戻し、終対象の Hom の一意性を使う。
規約：元の二頂点と全射の類。使われ方：上下対角の実代表の厳密な一致への入力。 -/
lemma dgOdotMilnorNuNullIntervalComponentMap_hom_ext (h : DGGluingMilnorSquare R d)
    (x y : (DGOdotMilnorNuNullIntervalComponent R d) _⦋0⦌)
    (f g : SSet.HomotopyCategory.mk
        ((dgOdotMilnorNuNullIntervalComponentMap R d).app (Opposite.op ⦋0⦌) x) ⟶
      SSet.HomotopyCategory.mk
        ((dgOdotMilnorNuNullIntervalComponentMap R d).app (Opposite.op ⦋0⦌) y)) : f = g := by
  have hc := dgOdotMilnorNuNullIntervalComponent_contractible R d h
  letI : KanComplex (DGOdotMilnorNuNullIntervalComponent R d) := hc.kanComplex
  have hb := IsFullyFaithful.homotopyCategoryMap_bijective
    (dgOdotMilnorNuNullIntervalComponentMap_isFullyFaithful R d) x y
  obtain ⟨a, ha⟩ := hb.2 f
  obtain ⟨b, hb⟩ := hb.2 g
  exact ha.symm.trans ((congrArg ((hoFunctor.map
    (dgOdotMilnorNuNullIntervalComponentMap R d)).toFunctor.map)
      ((hc.isTerminalVertex y).isTerminalHo.hom_ext a b)).trans hb)
end SerrePositivity.KST.SConstruction
