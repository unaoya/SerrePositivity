module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeFunctor
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeFunctorLift
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeYoneda
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectYoneda

/-!
概要：元 Hom gluing の実 cone の逆 shift と、その全像を保つ小さい dg 模型を構成する。
方針：既存の全 Hom cone 関手と真の dg shift を合成し、同じ実像を小包絡に入れる。
規約：同型な小代表への選択を使わない。使われ方：LT 普遍差の逆回転を実 dg 関手にする。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)

/-- 概要：元の実 cone の逆 shift を全 Hom で保持する厳密 dg 関手。
方針：既存 cone 関手と既存 perfect dg shift を合成。
規約：全次数作用を保持。使われ方：逆回転の始域成分。 -/
def dgHomGluingLoopConeFunctor : DGFunctor R (L) (PerfectDGModule R E) :=
  (dgHomGluingConeFunctor R C D E p q).comp (perfectDGModuleShiftDG R E Set.univ (-1))

/-- 概要：元左対象の二重 shift を同じ全 Hom で保持する。
方針：元左 Yoneda 関手に shift 1 と逆 shift を順に合成する。
規約：同型な対象へ選び直さない。使われ方：指定比較を保つ実逆回転の右成分。 -/
def dgHomGluingDoubleShiftLeftFunctor : DGFunctor R (L) (PerfectDGModule R E) :=
  ((((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)).comp p).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R E)).comp (perfectDGModuleShiftDG R E Set.univ 1)).comp
      (perfectDGModuleShiftDG R E Set.univ (-1))

/-- 概要：逆 shift cone と元左対象の二重 shift の二つの実像を保持する。
方針：元の同じ二実像を小さい和型で添字付ける。
規約：対象を変更しない。使われ方：実逆回転の共通 dg 基底。 -/
def dgHomGluingLoopConeFamily : (L) ⊕ (L) → PerfectDGModule R E :=
  Sum.elim (dgHomGluingLoopConeFunctor R C D E p q).obj
    (dgHomGluingDoubleShiftLeftFunctor R C D E p q).obj

/-- 概要：同じ逆 shift cone と二重 shift の全実像を保持する小さい模型。
方針：元の二実像を指定追加族にする。規約：全 Perf の Small 性を仮定しない。
使われ方：逆回転の二成分の共通 dg 基底。 -/
abbrev DGHomGluingLoopConeBase :=
  DGSmallPerfectEnvelope R E ((L) ⊕ (L)) (dgHomGluingLoopConeFamily R C D E p q)

/-- 概要：同じ逆 shift cone 関手を元の全実像を持つ小模型に制限する。
方針：元の対象・全 Hom 作用をそのまま持ち込む。
規約：元の cone を保持。使われ方：逆回転の左成分。 -/
def dgHomGluingLoopConeSmall :
    DGFunctor R (L) (DGHomGluingLoopConeBase R C D E p q) :=
  dgSmallPerfectEnvelopeFunctorLift R E ((L) ⊕ (L))
    (dgHomGluingLoopConeFamily R C D E p q)
    (dgHomGluingLoopConeFunctor R C D E p q) Sum.inl (fun _ => rfl)

/-- 概要：元左対象の代表加群を同じ小模型で全 Hom 自然に保持する。
方針：元左射影・元 p・同じ代表加群の包含を合成。
規約：同じ左対象を保持。使われ方：元左対象との指定回収。 -/
def dgHomGluingLoopConeTarget :
    DGFunctor R (L) (DGHomGluingLoopConeBase R C D E p q) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)).comp p).comp
    (dgSmallPerfectEnvelopeYoneda R E ((L) ⊕ (L))
      (dgHomGluingLoopConeFamily R C D E p q))

/-- 概要：元左対象の二重 shift を同じ実像小模型で保持する。
方針：元の実像族の右ラベルと元全 Hom 写像を使う。
規約：指定 shift を保つ。使われ方：実逆回転の右成分。 -/
def dgHomGluingLoopConeShiftedTarget :
    DGFunctor R (L) (DGHomGluingLoopConeBase R C D E p q) :=
  dgSmallPerfectEnvelopeFunctorLift R E ((L) ⊕ (L))
    (dgHomGluingLoopConeFamily R C D E p q)
    (dgHomGluingDoubleShiftLeftFunctor R C D E p q) Sum.inr (fun _ => rfl)

/-- 概要：同じ小さい左成分の包含後は元の全逆 shift cone 関手。
方針：元全像小模型の同じ包含を計算する。規約：全 dg 関手の等号。
使われ方：元実 cone と ν 像の全比較。 -/
lemma dgHomGluingLoopConeSmall_inclusion :
    (dgHomGluingLoopConeSmall R C D E p q).comp
      (dgSmallPerfectEnvelopeInclusion R E ((L) ⊕ (L))
        (dgHomGluingLoopConeFamily R C D E p q)) =
      dgHomGluingLoopConeFunctor R C D E p q :=
  dgSmallPerfectEnvelopeFunctorLift_inclusion R E ((L) ⊕ (L))
    (dgHomGluingLoopConeFamily R C D E p q)
    (dgHomGluingLoopConeFunctor R C D E p q) Sum.inl (fun _ => rfl)

/-- 概要：同じ右成分の包含後は元左対象の同じ二重 shift 関手。
方針：元二実像小模型の包含を計算する。規約：全 dg 関手の等号。
使われ方：元左対象と指定 shift 比較の回収。 -/
lemma dgHomGluingLoopConeShiftedTarget_inclusion :
    (dgHomGluingLoopConeShiftedTarget R C D E p q).comp
      (dgSmallPerfectEnvelopeInclusion R E ((L) ⊕ (L))
        (dgHomGluingLoopConeFamily R C D E p q)) =
      dgHomGluingDoubleShiftLeftFunctor R C D E p q :=
  dgSmallPerfectEnvelopeFunctorLift_inclusion R E ((L) ⊕ (L))
    (dgHomGluingLoopConeFamily R C D E p q)
    (dgHomGluingDoubleShiftLeftFunctor R C D E p q) Sum.inr (fun _ => rfl)
end SerrePositivity.KST.SConstruction
