module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLiftFunctor
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：元の dg 関手の全 Hom 準同型性は、任意の独立な対象宇宙の持ち上げで同値である。
方針：Hom 複体の写像は元のままであり、上げ下げした対象で検査する。
規約：係数宇宙を固定し、対象の Small 仮定を追加しない。
使われ方：D-17 の生成判定を追加 ULift 宇宙へ運ぶ。
-/
@[expose] public section
universe u v w r s
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {D : Type w} [DGCategory R D]

lemma dgUniverseLiftFunctor_homQuasiIso_iff (F : DGFunctor R C D) :
    HomQuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, r, s} F) ↔ HomQuasiIso F :=
  ⟨fun h x y => h ⟨ULift.up x⟩ ⟨ULift.up y⟩,
    fun h x y => h x.label.down y.label.down⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
