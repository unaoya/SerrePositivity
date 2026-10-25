module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroCornerComparison

/-!
概要：標準零角からの任意の完全 Hom を元核への前合成で同じ零成分へ置く。
方針：元の toZeroCategory と完全射の零対象保存を使う。
規約：元の全高次 Hom を保持。使われ方：実零角比較の上辺の混合零 Hom。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：標準零角からの完全射を元核の toZeroCategory で前合成する。
方針：元二射の基礎写像を合成する。
規約：元核と元終域を固定。使われ方：混合上辺の元完全合成。 -/
def dgOdotMilnorNuStandardZeroComposite (f : ExactMap zeroCategory.{u + 1} (B)) :
    ExactMap (K) (B) where
  hom := (toZeroCategory (K)).hom ≫ f.hom
  isExact := @isExactFunctor_comp _ _ _ _ _ (toZeroCategory (K)).isExact f.isExact

/-- 概要：標準零角からの全完全 Hom の元核による前合成。
方針：同じ豊穣前合成作用を使う。
規約：元の全高次 Hom を保持。使われ方：混合上面の全零性。 -/
def dgOdotMilnorNuStandardZeroNullHom :
    SimplicialCategory.sHom (C := StableQCat.{u + 1}) zeroCategory.{u + 1} (B) ⟶
      SimplicialCategory.sHom (C := StableQCat.{u + 1}) (K) (B) :=
  eHomWhiskerRight (C := StableQCat.{u + 1}) SSet (toZeroCategory (K)) (B)

/-- 概要：同じ前合成の元 Hom 頂点は同じ実完全合成の頂点。
方針：豊穣前合成の単位評価を使う。
規約：元の完全射を保持。使われ方：全 Hom 像の終関手性。 -/
lemma dgOdotMilnorNuStandardZeroNullHom_vertex (f : ExactMap zeroCategory.{u + 1} (B)) :
    (dgOdotMilnorNuStandardZeroNullHom R d ≫
      (quasicategoryCore (exactFunctors (K) (B) : SSet.{u + 1})).ι).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' (C := StableQCat.{u + 1}) zeroCategory.{u + 1} (B) f) =
      exactFunctorVertexEquiv (K) (B) (dgOdotMilnorNuStandardZeroComposite R d f) := by
  rfl

/-- 概要：標準零角を経由する全 Hom 像の全頂点は終関手。
方針：元 Hom 頂点を完全射へ戻し、同じ零対象保存を点ごとに使う。
規約：元高次 Hom 全像の制限。使われ方：指定上混合面の零成分。 -/
lemma dgOdotMilnorNuStandardZeroNullHom_vertex_isTerminal
    (a : (SimplicialCategory.sHom
      (C := StableQCat.{u + 1}) zeroCategory.{u + 1} (B)) _⦋0⦌) :
    IsTerminalVertex ((dgOdotMilnorNuStandardZeroNullHom R d ≫
      (quasicategoryCore (exactFunctors (K) (B) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) a) := by
  let f : ExactMap zeroCategory.{u + 1} (B) := (SimplicialCategory.homEquiv'
    (C := StableQCat.{u + 1}) zeroCategory.{u + 1} (B)).symm a
  have ha : SimplicialCategory.homEquiv' (C := StableQCat.{u + 1})
      zeroCategory.{u + 1} (B) f = a := Equiv.apply_symm_apply _ _
  have ht : IsTerminalVertex (exactFunctorVertexEquiv (K) (B)
      (dgOdotMilnorNuStandardZeroComposite R d f)) := by
    apply (isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
    change IsTerminalVertex (functorVertex ((toZeroCategory (K)).hom ≫ f.hom))
    exact isTerminalVertex_functorVertex_of_pointwise _ (fun x =>
      (@IsExactFunctor.preservesZero _ _ f.hom f.isExact _ (zeroCategory_isZero _)).2)
  exact ha ▸ (dgOdotMilnorNuStandardZeroNullHom_vertex R d f).symm ▸ ht

/-- 概要：標準零角経由の全 Hom を同じ固定 ν の零成分へ置く。
方針：全頂点の終関手性で元の前合成写像を制限する。
規約：元の全高次単体を保持。使われ方：指定零角比較の混合 Hom。
-/
def dgOdotMilnorNuStandardZeroNullFactor :
    SimplicialCategory.sHom (C := StableQCat.{u + 1}) zeroCategory.{u + 1} (B) ⟶
      DGOdotMilnorNuNullCoherenceSpace R d :=
  fullSubcomplexLift IsTerminalVertex (dgOdotMilnorNuStandardZeroNullHom R d ≫
    (quasicategoryCore (exactFunctors (K) (B) : SSet.{u + 1})).ι)
    (dgOdotMilnorNuStandardZeroNullHom_vertex_isTerminal R d)

/-- 概要：標準零角の全零因子分解は同じ元前合成 Hom を厳密回収する。
方針：同じ core 包含の単射性で元の持ち上げ式を戻す。
規約：全単体の等号。使われ方：指定上混合面の保持。 -/
lemma dgOdotMilnorNuStandardZeroNullFactor_hom (h : DGGluingMilnorSquare R d) :
    dgOdotMilnorNuStandardZeroNullFactor R d ≫ dgOdotMilnorNuNullCoherenceHom R d h =
      dgOdotMilnorNuStandardZeroNullHom R d := by
  apply (cancel_mono (quasicategoryCore (exactFunctors (K) (B) : SSet.{u + 1})).ι).mp
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => dgOdotMilnorNuStandardZeroNullFactor R d ≫ f)
      (dgOdotMilnorNuNullCoherenceHom_inclusion R d h))

end SerrePositivity.KST.SConstruction
