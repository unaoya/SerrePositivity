module
public import SerrePositivity.KST.SConstruction.Cofinality.CanonicalWideNaturality
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelDiagram

/-!
概要：元の具体的 wide 成分図式を元の K₀ 余核図式と自然に同定する。
方針：全 S 多次数の元の構造射を束ね、各段の障害群同型の自然性を使う。
規約：成分だけを独立に同定せず、全ての面と退化を保持する。
使われ方：離散的障害の bar 図式との全単体的な比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：具体的な元の wide 模型を全 S 多次数の厳密な図式に束ねる。
方針：元の構造射の単体の値で恒等・合成則を検査する。
規約：全多次数の同じ元の指定射の全辺模型を使う。
使われ方：成分を取る前の障害図式。 -/
def completionCanonicalWideDiagram (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u} where
  obj ι := LocalizingInvariants.completionCofiberWide (((multiSEndofunctor r).obj ι).map f).val
  map α := completionCanonicalWideStructureMap r α f hf
  map_id ι := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact congrArg (fun q : ((multiSEndofunctor r).obj ι) ⟶
        ((multiSEndofunctor r).obj ι) => (q.app Y).val.app n s.val)
      ((multiSEndofunctor r).map_id ι)
  map_comp {ι κ μ} α β := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact congrArg (fun q : ((multiSEndofunctor r).obj ι) ⟶
        ((multiSEndofunctor r).obj μ) => (q.app Y).val.app n s.val)
      ((multiSEndofunctor r).map_comp α β)

/-- 概要：元の wide 成分を全多単体図式として保持する。
方針：具体的 wide 図式に元の成分関手を適用する。
規約：各多次数で選び直した離散模型は使わない。
使われ方：K₀ 余核図式との自然同型の始域。 -/
def completionWideComponentDiagram (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ Type u :=
  completionCanonicalWideDiagram r f hf ⋙ SSet.π₀Functor

/-- 概要：元の wide 成分図式は元の K₀ 余核図式と全多次数で自然に同型。
方針：実装した障害群同型を全構造射の自然性で束ねる。
規約：底の集合の同型も元の障害写像そのもの。
使われ方：相対実現の離散的障害と bar 図式の全単体比較。 -/
def completionWideComponentCokernelNatIso (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionWideComponentDiagram r f hf ≅
      completionKZeroCokernelDiagram r f ⋙ forget AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun ι => (completionWideKZeroObstructionEquiv r ι f hf).toEquiv.toIso) (by
      intro ι κ α
      apply ConcreteCategory.hom_ext
      intro a
      exact completionCanonicalWideStructureMap_obstruction r α f hf a)

end SerrePositivity.KST.SConstruction.Cofinality
