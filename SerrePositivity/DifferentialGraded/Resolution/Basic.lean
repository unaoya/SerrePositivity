module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Tensor.ObjectwiseKFlat

/-! # 指定された小さいK-flat dg圏解像度

存在はこのデータ型の定義に含めない。元のdg圏のHomにK-flat性を課さない。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- dg圏の解像度版で使う、局所K-flatなdg圏と準同値の指定。 -/
structure KFlatDGResolution where
  source : Type w
  [sourceDG : DGCategory A source]
  [smallSource : Small.{u} source]
  augmentation : DGFunctor A source D
  quasiEquivalence : QuasiEquivalence augmentation
  homKFlat : localHomKFlat A source

attribute [instance] KFlatDGResolution.sourceDG KFlatDGResolution.smallSource

namespace KFlatDGResolution

/-- 既に局所K-flatな小さいdg圏は恒等準同値を解像度として使える。 -/
def refl [Small.{u} D] (hD : localHomKFlat A D) : KFlatDGResolution.{u, v, v} A D where
  source := D
  augmentation := DGFunctor.id D
  quasiEquivalence := quasiEquivalence_id
  homKFlat := hD

variable {A D}

/-- 既に与えられた準同値からの構成。準同値の存在自体は主張しない。 -/
def ofQuasiEquivalence (S : Type w) [DGCategory A S] [Small.{u} S]
    (p : DGFunctor A S D) (hp : QuasiEquivalence p) (hS : localHomKFlat A S) :
    KFlatDGResolution.{u, v, w} A D where
  source := S
  augmentation := p
  quasiEquivalence := hp
  homKFlat := hS

variable {E : Type z} [DGCategory A E]

/-- 準同値の標的を変えても同じK-flatな解像度圏を使える。 -/
def postcompose (P : KFlatDGResolution.{u, v, w} A D)
    (f : DGFunctor A D E) (hf : QuasiEquivalence f) : KFlatDGResolution.{u, z, w} A E where
  source := P.source
  augmentation := DGFunctor.comp P.augmentation f
  quasiEquivalence := quasiEquivalence_comp P.augmentation f P.quasiEquivalence hf
  homKFlat := P.homKFlat

end KFlatDGResolution
end SerrePositivity.DifferentialGraded
