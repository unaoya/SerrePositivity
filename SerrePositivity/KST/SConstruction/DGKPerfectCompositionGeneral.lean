module
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalence
public import SerrePositivity.DifferentialGraded.Verdier.DerivedGraphComposition
public import SerrePositivity.DifferentialGraded.Morita.PerfectFunctoriality

/-!
概要：元の主 Perf 延長の合成同型と合成の同値判定を供給する dg 一般入口。
方針：D の導来合成同型と主 Perf 制限だけを使い、既存の型と証明本文を保つ。
規約：∞ 圏・スペクトル・S 構成本体を import しない。
使われ方：D-17 の循環しない供給入口と旧 DGKPerfectComposition の互換公開。
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
