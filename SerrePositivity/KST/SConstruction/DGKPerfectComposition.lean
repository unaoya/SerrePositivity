module
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaEquivalence
public import SerrePositivity.DifferentialGraded.Verdier.DerivedGraphComposition
public import SerrePositivity.DifferentialGraded.Morita.PerfectFunctoriality

/-! # 固定 dg 入力の元の主 Perf 延長の合成比較
概要：同じ実導来延長を主 Perf に制限し、元の合成射の Morita 性を移す。
方針：D の導来合成同型と既存の Perf 制限を合成する。
規約：厳密等号や高次整合性を追加しない。使われ方：S の対象宇宙変更。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (T : Type z) [DGCategory R T] [Small.{u} T]
  (F : DGFunctor R D E) (G : DGFunctor R E T)

/-- 同じ元の主 Perf 延長の二回合成と、元の合成射の一回延長の自然同型。 -/
def dgKPerfectExtensionCompositionIso :
    quasiEquivalencePerfectExtension R D E F ⋙ quasiEquivalencePerfectExtension R E T G ≅
      quasiEquivalencePerfectExtension R D T (F.comp G) :=
  Morita.perfectFunctorCompositionIso R D E T
    (dgDerivedExtension R D E F) (dgDerivedExtension R E T G)
    (fun _ h => dgDerivedExtension_perfect R D E F h)
    (fun _ h => dgDerivedExtension_perfect R E T G h) ≪≫
  Morita.perfectFunctorIso R D T _ _
    (fun _ h => dgDerivedExtension_perfect R E T G (dgDerivedExtension_perfect R D E F h))
    (fun _ h => dgDerivedExtension_perfect R D T (F.comp G) h)
    (derivedGraphExtensionCompositionIso R D E T F G)

/-- 元の二射が主 Perf 上の同値なら、同じ元の合成射も主 Perf 上の同値。 -/
lemma dgKPerfectExtension_comp_isEquivalence
    [(quasiEquivalencePerfectExtension R D E F).IsEquivalence]
    [(quasiEquivalencePerfectExtension R E T G).IsEquivalence] :
    (quasiEquivalencePerfectExtension R D T (F.comp G)).IsEquivalence :=
  Functor.isEquivalence_of_iso (dgKPerfectExtensionCompositionIso R D E T F G)

end SerrePositivity.KST.SConstruction
