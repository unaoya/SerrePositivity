module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingHomAcyclic

/-! # 商の指定対象に接する Hom 複体の収縮

概要：Drinfeld 商で殺す対象に入る／出る全 Hom 複体を明示的に収縮する。
方針：ε の微分が単位となる式を、一般の収縮対象の Hom の鎖ホモトピーへ適用する。
規約：path 商のこの性質には K-flat 性は不要。使われ方：β3 の nerve の零化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D)

/-- 指定対象への Hom 複体の恒等射の零ホモトピー。 -/
def dgQuotientTargetHomotopy (x : DGQuotient.QuotientObject D P) (b : P) :
    Homotopy (𝟙 (homObject A (DGQuotient.QuotientObject D P) x ⟨b.val⟩)) 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingTargetHomotopy (DGQuotient.epsilonElement A D P b)
    (DGQuotient.differential_epsilonElement A D P b)

/-- 指定対象からの Hom 複体の恒等射の零ホモトピー。 -/
def dgQuotientSourceHomotopy (b : P) (y : DGQuotient.QuotientObject D P) :
    Homotopy (𝟙 (homObject A (DGQuotient.QuotientObject D P) ⟨b.val⟩ y)) 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingSourceHomotopy (DGQuotient.epsilonElement A D P b)
    (DGQuotient.differential_epsilonElement A D P b)

/-- 指定対象への Hom 複体は非輪状。 -/
lemma dgQuotientTargetHom_acyclic (x : DGQuotient.QuotientObject D P) (b : P) :
    (homObject A (DGQuotient.QuotientObject D P) x ⟨b.val⟩).Acyclic :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingTargetHom_acyclic (DGQuotient.epsilonElement A D P b)
    (DGQuotient.differential_epsilonElement A D P b)

/-- 指定対象からの Hom 複体は非輪状。 -/
lemma dgQuotientSourceHom_acyclic (b : P) (y : DGQuotient.QuotientObject D P) :
    (homObject A (DGQuotient.QuotientObject D P) ⟨b.val⟩ y).Acyclic :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.contractingSourceHom_acyclic (DGQuotient.epsilonElement A D P b)
    (DGQuotient.differential_epsilonElement A D P b)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
