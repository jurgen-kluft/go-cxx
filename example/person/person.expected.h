#pragma once

namespace nperson
{
    struct Person
    {
        int   age = 0;
        float health = 0.0f;
        int   iq = 42;

        inline int GetAge() { return age; }
        inline float GetHealth() { return health; }
        inline int GetIq() { return iq; }
        inline void Grow() { age++; }

        inline auto GetAgeAdder()
        {
            return [age = this->age](int i) { return age + i; };
        }
    };

    int Population = 0;

    inline Person NewPerson(int age, float health, int iq)
    {
        ++Population;
        return Person{age, health, iq};
    }

}  // namespace person
