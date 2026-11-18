module

public import SerrePositivity.EInfinity.Modules.TensorSimplices
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.TruncatedDoldKanFunctor

/-!
# 同じ加群の全 source frame Hom と元の dg Hom の Dold–Kan

概要：M10 の同じ正規化単体テンソルからの全 Hom を元の主 Hom end に同定する。
方針：既存の tensor/Hom 転置と正規化単体の Hom 同値を全単体で合成する。
規約：HA 1.3.1.13、Kerodon 2.5.9（Tag 00SC）、零次数は smart 切断の閉元。
使われ方：実モデル frame Hom と指定 dg nerve の写像空間の全標的比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ転置は係数の全ての前合成に自然。
方針：既存の逆転置の自然性を両逆の式で同じ転置へ戻す。
規約：HA 1.3.1.13、元の射。使われ方：全ての面・退化との可換性。 -/
lemma moduleParamCurry_precompose {K L : Complex A} {P N : ModuleCategory A D}
    (g : K ⟶ L) (f : moduleTensorLeftObj A D L P ⟶ N) :
    moduleParamCurry A D (tensorModuleMap g (ForgetEnrichment.to (Complex A) P) ≫ f) =
      g ≫ moduleParamCurry A D f := by
  apply moduleParamUncurry_injective (M := P) (N := N)
  calc
    _ = tensorModuleMap g (ForgetEnrichment.to (Complex A) P) ≫ f :=
      moduleParamUncurry_curry A D _
    _ = tensorModuleMap g (ForgetEnrichment.to (Complex A) P) ≫
        moduleParamUncurry A D (moduleParamCurry A D f) :=
      congrArg (fun z => tensorModuleMap g (ForgetEnrichment.to (Complex A) P) ≫ z)
        (moduleParamUncurry_curry A D f).symm
    _ = _ := moduleParamUncurry_precomp A D g (moduleParamCurry A D f)

/-- 概要：同じ source frame の一つの全単体 Hom は元の dg Hom の実 Dold–Kan 各項。
方針：元の転置と既存の正規化単体 Hom 同値を合成する。
規約：HA 1.3.1.13、全次元。使われ方：同じ全単体同型の成分。 -/
def moduleTensorSimplexHomEquiv (P N : ModuleCategory A D) (n : SimplexCategory) :
    (((moduleTensorSimplicesFunctor A D).obj P).obj n ⟶ N) ≃
      (doldKanHomModule (R := A) (D := RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)).obj (op n) :=
  (moduleTensorHomEquiv A D P ((BarrattEccles.normalizedFunctor A).obj
    (SSet.stdSimplex.obj n)) N).trans
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A
        (moduleHom A D (ForgetEnrichment.to (Complex A) P)
          (ForgetEnrichment.to (Complex A) N)) n)

/-- 概要：同じ全単体 Hom は元の主 Hom end の Dold–Kan 単体集合と同型。
方針：同じ係数前合成の自然性を全単体同値に付ける。
規約：HA 1.3.1.13、零次数だけに制限しない。使われ方：元の dg 写像空間比較。 -/
def moduleTensorHomDoldKanIso (P N : ModuleCategory A D) :
    (cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P)).obj N ≅
      doldKanHomSpace (R := A) (D := RightModule A D)
        (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N) :=
  NatIso.ofComponents (fun n => Equiv.toIso (moduleTensorSimplexHomEquiv A D P N n.unop)) (by
    intro n m f
    apply ConcreteCategory.hom_ext
    intro α
    change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A
      (moduleHom A D (ForgetEnrichment.to (Complex A) P)
        (ForgetEnrichment.to (Complex A) N)) m.unop
      (moduleParamCurry A D
        (tensorModuleMap ((BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map f.unop))
          (ForgetEnrichment.to (Complex A) P) ≫ α)) = _
    rw [moduleParamCurry_precompose A D (P := P) (N := N)]
    exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_naturality A _ f.unop _)

/-- 概要：同じ全単体 Hom 比較は元の全ての標的加群射に自然な同型。
方針：転置の後合成自然性と実 Dold–Kan の同じ chain map を使う。
規約：HA 1.3.1.13、全標的。使われ方：モデル frame からの比較の全関手。 -/
def moduleTensorHomDoldKanNatIso (P : ModuleCategory A D) :
    cosimplicialHom ((moduleTensorSimplicesFunctor A D).obj P) ≅
      (eHomFunctor (Complex A) (ModuleCategory A D)).obj (op P) ⋙
        _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A :=
  NatIso.ofComponents (moduleTensorHomDoldKanIso A D P) (by
    intro M N g
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A
      (moduleHom A D (ForgetEnrichment.to (Complex A) P)
        (ForgetEnrichment.to (Complex A) N)) n.unop (moduleParamCurry A D (f ≫ g)) = _
    rw [moduleParamCurry_postcompose A D (M := P) (N := M) (P := N)]
    exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp A n.unop (moduleParamCurry A D f)
      (eHomWhiskerLeft (Complex A) P g))

end SerrePositivity.EInfinity.Modules
