module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActionComparisonHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActionComparisonSquareHomTransfer
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompositionHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatHomComparisonNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedNaturalityTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatCompositorCoherence
/-!
概要：元の指定導来合成子 κ の任意双加群射に対する二変数自然性を証明する。
方針：元の ξ の水平二重比較と指定合成子四角形を保ち、全前合成から反映する。
規約：四端の右相対 K-flat 性を明示し、射の可逆性を要求しない。
使われ方：指定模型の変更と一般 cell 模型の coherence の移送。
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (D E F : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R F] [Small.{u} F]
private lemma compositor_comparison (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R F E)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E Q) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P Q hP).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D F (BimoduleTensor.compose R F E D Q P)
        (_root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q P hQ hP) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q hQ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R E F Q hQ) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P Q hP hQ).postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R F) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso, Iso.trans_assoc] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositor_iso R D E F P Q hP hQ
variable {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R F E}
local notation "P₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P
local notation "P₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'
local notation "Q₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q
local notation "Q₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'
variable (f : P ⟶ P') (g : Q ⟶ Q')
  (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
  (hP' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P'))
  (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q))
  (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R F E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R F E Q'))
local notation "C₀" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E D Q₀ P₀
local notation "C₁" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R F E D Q₁ P₁
local notation "hC₀" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₀ P₀ hQ hP
local notation "hC₁" => _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat_compose R F E D Q₁ P₁ hQ' hP'
local notation "L₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D
local notation "L₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E
local notation "L₂" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R F
local notation "F₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P₀
local notation "F₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P₁
local notation "H₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F Q₀
local notation "H₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F Q₁
local notation "G₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₀ hP
local notation "G₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P₁ hP'
local notation "K₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₀ hQ
local notation "K₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R E F Q₁ hQ'
local notation "T₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D F C₀
local notation "T₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D F C₁
local notation "U₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D F C₀ hC₀
local notation "U₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D F C₁ hC₁
local notation "xP₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P₀ hP
local notation "xP₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P₁ hP'
local notation "xQ₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R E F Q₀ hQ
local notation "xQ₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R E F Q₁ hQ'
local notation "xC₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D F C₀ hC₀
local notation "xC₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D F C₁ hC₁
local notation "e" =>
  CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E) f
local notation "d" =>
  CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R E F) g
local notation "e₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D E f hP hP'
local notation "d₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R E F g hQ hQ'
local notation "c" => _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R F E D g f
local notation "t" =>
  CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D F) c
local notation "u" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleHom R D F c hC₀ hC₁
local notation "k₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P₀ Q₀ hP
local notation "k₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F P₁ Q₁ hP'
local notation "a₀" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₀ Q₀ hP hQ
local notation "a₁" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso R D E F P₁ Q₁ hP' hQ'
local notation "jD" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp F₀ F₁ H₀ e ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp H₀ H₁ F₁ d
local notation "jK" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp G₀ G₁ K₀ e₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp K₀ K₁ G₁ d₀
include hP hP' hQ hQ' in
lemma dgKernelDerivedInfinity_compIso_hom_naturality_precomp :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (F₀ ≫ H₀) T₁ L₀ ((k₀).hom ≫ t) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (F₀ ≫ H₀) T₁ L₀ (jD ≫ (k₁).hom) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso_hom_naturality L₀ L₁ L₂ F₀ F₁ H₀ H₁ G₀ G₁ K₀ K₁
    xP₀ xP₁ xQ₀ xQ₁ e e₀ d d₀
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_hom_naturality R D E f hP hP')
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_hom_naturality R E F g hQ hQ')
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso_hom_naturality R D F c hC₀ hC₁
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelCompositionIso_naturality_hom R D E F f g hP hP' hQ hQ'
  have hat := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_iso_square a₀ a₁ jK u L₂
    (by simpa only [Category.assoc] using! ha)
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonSquare_transfer_hom_naturality xC₀ xC₁
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₁ L₂ F₀ G₀ H₀ K₀ xP₀ xQ₀)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.comparisonCompositionIso L₀ L₁ L₂ F₁ G₁ H₁ K₁ xP₁ xQ₁)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp k₀ L₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp k₁ L₀)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (F₀ ≫ H₀) (F₁ ≫ H₁) L₀ jD)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (G₀ ≫ K₀) (G₁ ≫ K₁) L₂ jK)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp T₀ T₁ L₀ t) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp U₀ U₁ L₂ u)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp a₀ L₂) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp a₁ L₂)
    (compositor_comparison R D E F P₀ Q₀ hP hQ)
    (compositor_comparison R D E F P₁ Q₁ hP' hQ') hn hx hat
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_iso_square k₀ k₁ jD t L₀ hs
include hP hP' hQ hQ' in
lemma dgKernelDerivedInfinity_compIso_hom_naturality :
    (k₀).hom ≫ t = jD ≫ (k₁).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_eq_of_isFullyFaithful L₀
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution_precomposition_isFullyFaithful R D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R F)) _ _
    (dgKernelDerivedInfinity_compIso_hom_naturality_precomp R D E F f g hP hP' hQ hQ')
end SerrePositivity.InfinityCategories.Project.DerivedCategories
